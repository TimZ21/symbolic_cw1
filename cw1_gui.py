"""
Interactive GUI wrapper around the Z3-based exam timetabling solver.

Users can enter problem parameters manually instead of loading them from a
text file, then visualise the resulting timetable in multiple views.
"""

from __future__ import annotations

import tkinter as tk
from tkinter import filedialog, messagebox, ttk
from tkinter.scrolledtext import ScrolledText
from collections import defaultdict
from dataclasses import dataclass, field
from time import perf_counter
from typing import Dict, List, Tuple
import re

from z3 import (
    And,
    AtMost,
    Bool,
    BoolRef,
    If,
    Not,
    Or,
    Solver,
    Sum,
    is_true,
    sat,
)


# Default constraint parameters used unless the user overrides them in the GUI.
DEFAULT_SLOTS_PER_DAY = 4
DEFAULT_MIN_GAP = 1
DEFAULT_TURNAROUND_GAP = 1
DEFAULT_LARGE_EXAM_THRESHOLD = 10
DEFAULT_EXAMINER_CAPACITY = 10


@dataclass
class Instance:
    # Mirror the Instance structure from the CLI template so both entry points
    # feed the same solver logic.
    number_of_students: int = 0
    number_of_exams: int = 0
    number_of_slots: int = 0
    number_of_rooms: int = 0
    room_capacities: List[int] = field(default_factory=list)
    exams_to_students: List[Tuple[int, int]] = field(default_factory=list)


def load_instance_from_file(path: str) -> Instance:
    """Parse a text instance file using the template format."""

    def read_attribute(handle, name: str) -> int:
        line = handle.readline()
        if line == "":
            raise ValueError(f"Unexpected end of file while reading {name}.")
        match = re.match(rf"{name}:\s*(\d+)$", line.strip())
        if not match:
            raise ValueError(f"Could not parse line '{line.strip()}' for {name}.")
        return int(match.group(1))

    instance = Instance()
    with open(path, encoding="utf-8") as handle:
        instance.number_of_students = read_attribute(handle, "Number of students")
        instance.number_of_exams = read_attribute(handle, "Number of exams")
        instance.number_of_slots = read_attribute(handle, "Number of slots")
        instance.number_of_rooms = read_attribute(handle, "Number of rooms")

        for idx in range(instance.number_of_rooms):
            capacity = read_attribute(handle, f"Room {idx} capacity")
            instance.room_capacities.append(capacity)

        for line in handle:
            stripped = line.strip()
            if not stripped:
                continue
            match = re.match(r"^(\d+)\s+(\d+)$", stripped)
            if not match:
                raise ValueError(f"Failed to parse line '{stripped}'.")
            exam_id = int(match.group(1))
            student_id = int(match.group(2))
            instance.exams_to_students.append((exam_id, student_id))

    return instance

# Solve method to solve the basic and additional constraints
def solve(
    instance: Instance,
    *,
    slots_per_day: int = DEFAULT_SLOTS_PER_DAY,
    min_gap: int = DEFAULT_MIN_GAP,
    turnaround_gap: int = DEFAULT_TURNAROUND_GAP,
    large_exam_threshold: int = DEFAULT_LARGE_EXAM_THRESHOLD,
    invigilator_capacity: int = DEFAULT_EXAMINER_CAPACITY,
) -> Dict[str, object]:
    """Run the solver and return structured data for GUI consumption."""
    # Unpack the problem sizes and deep-copy mutable input collections.
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    # Input validation matches the original file-reading workflow.
    if any(val < 0 for val in (E, R, T, S)):
        raise ValueError("All problem sizes must be non-negative integers.")
    if slots_per_day <= 0:
        raise ValueError("Slots per day must be at least 1.")
    if min_gap < 0:
        raise ValueError("Minimum gap cannot be negative.")
    if turnaround_gap < 0:
        raise ValueError("Room turnaround gap cannot be negative.")
    if large_exam_threshold < 0:
        raise ValueError("Large exam threshold cannot be negative.")
    if invigilator_capacity < 0:
        raise ValueError("Invigilator capacity cannot be negative.")

    if len(caps) != R:
        raise ValueError("Number of room capacities must match the number of rooms.")

    for idx, cap in enumerate(caps):
        if cap < 0:
            raise ValueError(f"Room {idx} capacity must be non-negative.")
    # Ensure every (exam, student) pair references valid indices.
    for (e, s) in pairs:
        if not 0 <= e < E:
            raise ValueError(f"Exam id {e} out of range (expected 0..{E-1}).")
        if not 0 <= s < S:
            raise ValueError(f"Student id {s} out of range (expected 0..{S-1}).")

    # Build exam↔student incidence sets once and reuse for all constraints.
    students_by_exam: List[set[int]] = [set() for _ in range(E)]
    exams_by_student: List[set[int]] = [set() for _ in range(S)]
    for e, s in pairs:
        students_by_exam[e].add(s)
        exams_by_student[s].add(e)
    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Decision variables reuse the Bool matrix layout from cw1_template.py.
    X: List[List[List[BoolRef]]] = [
        [[Bool(f"X_e{e}_r{r}_t{t}") for t in range(T)] for r in range(R)]
        for e in range(E)
    ]
    Y: List[List[BoolRef]] = [
        [Bool(f"Y_e{e}_t{t}") for t in range(T)] for e in range(E)
    ]

    # Group every slot index by day for the "two exams per day" requirement.
    slots_by_day: Dict[int, List[int]] = defaultdict(list)
    for t in range(T):
        day = t // slots_per_day
        slots_by_day[day].append(t)

    solver = Solver()

    def _exactly_one(lits: List[BoolRef]) -> None:
        if not lits:
            solver.add(False)
        else:
            solver.add(AtMost(*lits, 1))
            solver.add(Or(lits))

    # Link the reduced Y variables to the detailed X placement variables.
    for e in range(E):
        for t in range(T):
            solver.add(Y[e][t] == Or([X[e][r][t] for r in range(R)]))

    # Each exam must select exactly one (room, slot) pair.
    for e in range(E):
        lits = [X[e][r][t] for r in range(R) for t in range(T)]
        _exactly_one(lits)

    # Block double-booking rooms in the same slot.
    for r in range(R):
        for t in range(T):
            lits = [X[e][r][t] for e in range(E)]
            if lits:
                solver.add(AtMost(*lits, 1))

    # Prevent oversubscribed rooms by hard-fixing infeasible placements to false.
    for e in range(E):
        size = exam_size[e]
        for r in range(R):
            if size > caps[r]:
                for t in range(T):
                    solver.add(Not(X[e][r][t]))

    # Student constraints: no clashes, honour minimum gaps, and avoid back-to-back exams.
    for sid in range(S):
        exams = sorted(exams_by_student[sid])
        for i in range(len(exams)):
            for j in range(i + 1, len(exams)):
                e1, e2 = exams[i], exams[j]
                for t in range(T):
                    solver.add(Not(And(Y[e1][t], Y[e2][t])))
                for gap in range(1, min_gap + 1):
                    for t in range(T - gap):
                        solver.add(Not(And(Y[e1][t], Y[e2][t + gap])))
                        solver.add(Not(And(Y[e1][t + gap], Y[e2][t])))

    # Limit each student to at most two exams per day.
    for sid in range(S):
        exams = list(exams_by_student[sid])
        for day_slots in slots_by_day.values():
            day_lits = [Y[e][t] for e in exams for t in day_slots]
            if day_lits:
                solver.add(AtMost(*day_lits, 2))

    # Enforce the room turnaround by preventing another exam within the gap window.
    for r in range(R):
        for gap in range(1, turnaround_gap + 1):
            for t in range(T - gap):
                used_now = Or([X[e][r][t] for e in range(E)])
                used_next = Or([X[e][r][t + gap] for e in range(E)])
                solver.add(Not(And(used_now, used_next)))

    # Prevent large exams from occupying the last slot of any day.
    last_slots: List[int] = []
    for t in range(T):
        if (t % slots_per_day) == slots_per_day - 1:
            last_slots.append(t)

    if last_slots:
        for e in range(E):
            if exam_size[e] >= large_exam_threshold:
                for t in last_slots:
                    solver.add(Not(Y[e][t]))

    # Limit invigilator usage per slot (2 by default, 3 for large exams).
    examiner_demand = [
        3 if exam_size[e] >= large_exam_threshold else 2
        for e in range(E)
    ]
    for t in range(T):
        demand_terms = [
            If(Y[e][t], examiner_demand[e], 0)
            for e in range(E)
        ]
        if demand_terms:
            solver.add(Sum(demand_terms) <= invigilator_capacity)

    # Solve the SAT model and record the elapsed time for display.
    t0 = perf_counter()
    res = solver.check()
    runtime_ms = (perf_counter() - t0) * 1000.0

    if res != sat:
        return {
            "status": "unsat",
            "runtime_ms": runtime_ms,
        }

    model = solver.model()

    # Recover a concrete room/slot pair per exam from the satisfying model.
    assignment: List[Tuple[int, int]] = [(-1, -1) for _ in range(E)]
    for e in range(E):
        found = False
        for r in range(R):
            for t in range(T):
                if is_true(model.evaluate(X[e][r][t], model_completion=True)):
                    assignment[e] = (r, t)
                    found = True
                    break
            if found:
                break
        if not found:
            raise RuntimeError(f"Model recovery failed for exam {e}.")

    # Group the assignments by slot for the slot-centric Treeview.
    schedule_by_slot: Dict[int, List[Tuple[int, int]]] = defaultdict(list)
    for exam, (room, slot) in enumerate(assignment):
        schedule_by_slot[slot].append((exam, room))

    return {
        "status": "sat",
        "runtime_ms": runtime_ms,
        "assignment": assignment,
        "schedule_by_slot": schedule_by_slot,
        "slots_per_day": slots_per_day,
    }


class ExamSchedulerGUI:
    """Tkinter-based front end that wraps the Boolean Z3 solver."""

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("Exam Timetable Solver")
        self.root.minsize(960, 600)

        self.students_var = tk.StringVar(value="0")
        self.exams_var = tk.StringVar(value="0")
        self.slots_var = tk.StringVar(value="0")
        self.rooms_var = tk.StringVar(value="0")

        self.slots_per_day_var = tk.StringVar(value=str(DEFAULT_SLOTS_PER_DAY))
        self.min_gap_var = tk.StringVar(value=str(DEFAULT_MIN_GAP))
        self.turnaround_gap_var = tk.StringVar(value=str(DEFAULT_TURNAROUND_GAP))
        self.large_exam_threshold_var = tk.StringVar(
            value=str(DEFAULT_LARGE_EXAM_THRESHOLD)
        )
        self.examiner_capacity_var = tk.StringVar(
            value=str(DEFAULT_EXAMINER_CAPACITY)
        )

        self.status_var = tk.StringVar(value="Result: waiting for input.")
        self.runtime_var = tk.StringVar(value="Runtime: -")

        self.room_capacity_vars: List[tk.StringVar] = []

        self._build_layout()
        self.refresh_room_entries()

    def _build_layout(self) -> None:
        """Construct the two-column layout that captures inputs and renders outputs."""
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)

        main = ttk.Frame(self.root, padding=12)
        main.grid(row=0, column=0, sticky="nsew")
        main.columnconfigure(0, weight=0)
        main.columnconfigure(1, weight=1)
        main.rowconfigure(0, weight=1)

        input_frame = ttk.Frame(main)
        input_frame.grid(row=0, column=0, sticky="nsew", padx=(0, 12))

        output_frame = ttk.Frame(main)
        output_frame.grid(row=0, column=1, sticky="nsew")
        output_frame.columnconfigure(0, weight=1)
        output_frame.rowconfigure(1, weight=1)

        # Left column: widgets to capture numeric counts and relationships.
        counts_group = ttk.LabelFrame(input_frame, text="Problem sizes")
        counts_group.pack(fill="x", pady=(0, 10))

        entries = [
            ("Number of students", self.students_var),
            ("Number of exams", self.exams_var),
            ("Number of slots", self.slots_var),
            ("Number of rooms", self.rooms_var),
        ]

        for idx, (label_text, var) in enumerate(entries):
            ttk.Label(counts_group, text=label_text).grid(
                row=idx, column=0, sticky="w", padx=4, pady=4
            )
            ttk.Entry(counts_group, textvariable=var, width=12).grid(
                row=idx, column=1, sticky="ew", padx=4, pady=4
            )
        counts_group.columnconfigure(1, weight=1)

        ttk.Button(
            counts_group,
            text="Update rooms",
            command=self.refresh_room_entries,
        ).grid(row=len(entries), column=0, columnspan=2, pady=(6, 2))

        self.room_group = ttk.LabelFrame(input_frame, text="Room capacities")
        self.room_group.pack(fill="x", pady=(0, 10))

        pairs_group = ttk.LabelFrame(input_frame, text="Exam/student pairs")
        pairs_group.pack(fill="both", expand=True)

        ttk.Label(
            pairs_group,
            text="Enter one pair per line as 'exam_id student_id' or 'exam_id,student_id'.",
        ).pack(anchor="w", padx=4, pady=(4, 2))

        self.pairs_text = ScrolledText(pairs_group, height=12, width=32, wrap="word")
        self.pairs_text.pack(fill="both", expand=True, padx=4, pady=(0, 4))

        # Optional overrides for the three "hard" constraints.
        advanced_group = ttk.LabelFrame(input_frame, text="Additional constraints")
        advanced_group.pack(fill="x", pady=(10, 10))

        advanced_entries = [
            ("Slots per day", self.slots_per_day_var),
            ("Minimum gap between exams", self.min_gap_var),
            ("Room turnaround gap", self.turnaround_gap_var),
            ("Large exam threshold", self.large_exam_threshold_var),
            ("Invigilator capacity per slot", self.examiner_capacity_var),
        ]

        for idx, (label_text, var) in enumerate(advanced_entries):
            ttk.Label(advanced_group, text=label_text).grid(
                row=idx, column=0, sticky="w", padx=4, pady=4
            )
            ttk.Entry(advanced_group, textvariable=var, width=12).grid(
                row=idx, column=1, sticky="ew", padx=4, pady=4
            )
        advanced_group.columnconfigure(1, weight=1)

        ttk.Button(
            input_frame,
            text="Load from file...",
            command=self.on_load_file,
        ).pack(fill="x", pady=(8, 0))

        ttk.Button(
            input_frame,
            text="Solve timetable",
            command=self.on_solve,
        ).pack(fill="x", pady=(4, 0))

        # Right column: status banner plus two tabbed visualisations.
        status_frame = ttk.Frame(output_frame)
        status_frame.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        status_frame.columnconfigure(1, weight=1)

        ttk.Label(status_frame, textvariable=self.status_var).grid(
            row=0, column=0, sticky="w"
        )
        ttk.Label(status_frame, textvariable=self.runtime_var).grid(
            row=0, column=1, sticky="e"
        )

        notebook = ttk.Notebook(output_frame)
        notebook.grid(row=1, column=0, sticky="nsew")

        # Tab 1: per-exam table mirroring the textual solver output.
        assignment_tab = ttk.Frame(notebook)
        slots_tab = ttk.Frame(notebook)
        notebook.add(assignment_tab, text="Assignments by exam")
        notebook.add(slots_tab, text="Schedule by slot")

        assignment_tab.columnconfigure(0, weight=1)
        assignment_tab.rowconfigure(0, weight=1)

        assignment_columns = ("exam", "room", "slot", "day", "slot_in_day")
        self.assignment_tree = ttk.Treeview(
            assignment_tab, columns=assignment_columns, show="headings", height=16
        )
        headings = {
            "exam": "Exam",
            "room": "Room",
            "slot": "Slot",
            "day": "Day",
            "slot_in_day": "Slot in day",
        }
        for col in assignment_columns:
            self.assignment_tree.heading(col, text=headings[col])
            anchor = "center" if col != "exam" else "w"
            self.assignment_tree.column(col, anchor=anchor, width=120, stretch=True)
        assignment_scroll = ttk.Scrollbar(
            assignment_tab, orient="vertical", command=self.assignment_tree.yview
        )
        self.assignment_tree.configure(yscrollcommand=assignment_scroll.set)
        self.assignment_tree.grid(row=0, column=0, sticky="nsew")
        assignment_scroll.grid(row=0, column=1, sticky="ns")

        slots_tab.columnconfigure(0, weight=1)
        slots_tab.rowconfigure(0, weight=1)

        # Tab 2: tree showing each slot with the exams scheduled inside it.
        self.slot_tree = ttk.Treeview(
            slots_tab, columns=("room", "exam"), show="tree headings", height=16
        )
        self.slot_tree.heading("#0", text="Slot")
        self.slot_tree.heading("room", text="Room")
        self.slot_tree.heading("exam", text="Exam")
        self.slot_tree.column("#0", width=220, stretch=True)
        self.slot_tree.column("room", width=100, anchor="center", stretch=False)
        self.slot_tree.column("exam", width=100, anchor="center", stretch=False)
        slot_scroll = ttk.Scrollbar(
            slots_tab, orient="vertical", command=self.slot_tree.yview
        )
        self.slot_tree.configure(yscrollcommand=slot_scroll.set)
        self.slot_tree.grid(row=0, column=0, sticky="nsew")
        slot_scroll.grid(row=0, column=1, sticky="ns")

    def refresh_room_entries(self) -> None:
        """Rebuild the capacity entry widgets to match the room count."""
        try:
            room_count = self._read_positive_int(self.rooms_var.get(), "Number of rooms")
        except ValueError:
            room_count = 0

        for child in self.room_group.winfo_children():
            child.destroy()
        self.room_capacity_vars.clear()

        if room_count == 0:
            ttk.Label(self.room_group, text="Set a positive number of rooms first.").pack(
                anchor="w", padx=4, pady=4
            )
            return

        for idx in range(room_count):
            var = tk.StringVar(value="0")
            self.room_capacity_vars.append(var)
            ttk.Label(self.room_group, text=f"Room {idx} capacity").grid(
                row=idx, column=0, sticky="w", padx=4, pady=2
            )
            ttk.Entry(self.room_group, textvariable=var, width=12).grid(
                row=idx, column=1, sticky="ew", padx=4, pady=2
            )
        self.room_group.columnconfigure(1, weight=1)

    def on_solve(self) -> None:
        """Collect user inputs, invoke the solver, and render the results."""
        try:
            instance = self._build_instance_from_inputs()
            slots_per_day = self._read_positive_int(
                self.slots_per_day_var.get(), "Slots per day"
            )
            min_gap = self._read_non_negative_int(
                self.min_gap_var.get(), "Minimum gap between exams"
            )
            turnaround_gap = self._read_non_negative_int(
                self.turnaround_gap_var.get(), "Room turnaround gap"
            )
            large_exam_threshold = self._read_non_negative_int(
                self.large_exam_threshold_var.get(), "Large exam threshold"
            )
            invigilator_capacity = self._read_non_negative_int(
                self.examiner_capacity_var.get(), "Invigilator capacity per slot"
            )
        except ValueError as exc:
            messagebox.showerror("Invalid input", str(exc), parent=self.root)
            return

        try:
            result = solve(
                instance,
                slots_per_day=slots_per_day,
                min_gap=min_gap,
                turnaround_gap=turnaround_gap,
                large_exam_threshold=large_exam_threshold,
                invigilator_capacity=invigilator_capacity,
            )
        except ValueError as exc:
            messagebox.showerror("Constraint error", str(exc), parent=self.root)
            return
        except RuntimeError as exc:
            messagebox.showerror("Solver error", str(exc), parent=self.root)
            return

        self._handle_solver_result(result)

    def on_load_file(self) -> None:
        """Choose a text file, populate the form, and solve with defaults."""
        filename = filedialog.askopenfilename(
            title="Open instance file",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
        )
        if not filename:
            return

        try:
            instance = load_instance_from_file(filename)
        except (OSError, ValueError) as exc:
            messagebox.showerror("Failed to load file", str(exc), parent=self.root)
            return

        self._populate_form_from_instance(instance)

        try:
            result = solve(instance)
        except (ValueError, RuntimeError) as exc:
            messagebox.showerror("Solver error", str(exc), parent=self.root)
            return

        self._handle_solver_result(result)

    def _build_instance_from_inputs(self) -> Instance:
        """Generate an Instance based on the current form contents."""
        students = self._read_positive_int(
            self.students_var.get(), "Number of students"
        )
        exams = self._read_positive_int(self.exams_var.get(), "Number of exams")
        slots = self._read_positive_int(self.slots_var.get(), "Number of slots")
        rooms = self._read_positive_int(self.rooms_var.get(), "Number of rooms")

        # Room widgets are dynamically created, so double-check the counts agree.
        if len(self.room_capacity_vars) != rooms:
            raise ValueError(
                "Room capacities are out of sync. Click 'Update rooms' after changing the room count."
            )

        capacities: List[int] = []
        for idx, var in enumerate(self.room_capacity_vars):
            capacity = self._read_non_negative_int(
                var.get(), f"Capacity for room {idx}"
            )
            capacities.append(capacity)

        # Parse the free-form exam/student pairs supplied in the text area.
        pairs_text = self.pairs_text.get("1.0", "end").strip()
        pairs: List[Tuple[int, int]] = []
        if pairs_text:
            for line_no, line in enumerate(pairs_text.splitlines(), start=1):
                raw = line.strip()
                if not raw or raw.startswith("#"):
                    continue
                tokens = re.split(r"[,\s]+", raw)
                if len(tokens) != 2:
                    raise ValueError(
                        f"Line {line_no}: expected exactly two integers per pair."
                    )
                try:
                    exam_id = int(tokens[0])
                    student_id = int(tokens[1])
                except ValueError:
                    raise ValueError(
                        f"Line {line_no}: exam and student ids must be integers."
                    ) from None
                pairs.append((exam_id, student_id))

        if not pairs:
            raise ValueError(
                "No exam/student pairs provided. Enter at least one pair in the text area."
            )

        # Feed the populated structure back to the solver wrapper.
        return Instance(
            number_of_students=students,
            number_of_exams=exams,
            number_of_slots=slots,
            number_of_rooms=rooms,
            room_capacities=capacities,
            exams_to_students=pairs,
        )

    def _populate_form_from_instance(self, instance: Instance) -> None:
        """Update all input widgets to match the provided instance."""
        self.students_var.set(str(instance.number_of_students))
        self.exams_var.set(str(instance.number_of_exams))
        self.slots_var.set(str(instance.number_of_slots))
        self.rooms_var.set(str(instance.number_of_rooms))

        self.refresh_room_entries()
        for var, capacity in zip(self.room_capacity_vars, instance.room_capacities):
            var.set(str(capacity))

        pairs_output = "\n".join(f"{exam} {student}" for exam, student in instance.exams_to_students)
        self.pairs_text.delete("1.0", "end")
        if pairs_output:
            self.pairs_text.insert("1.0", pairs_output)

    def _handle_solver_result(self, result: Dict[str, object]) -> None:
        """Common renderer for solver outcomes."""
        runtime_ms = result["runtime_ms"]  # type: ignore[index]
        self.runtime_var.set(f"Runtime: {runtime_ms:.3f} ms")

        if result["status"] != "sat":
            self.status_var.set("Result: UNSAT - no feasible timetable.")
            self._clear_output_tables()
            messagebox.showinfo(
                "Solver result",
                "No feasible timetable exists for the provided inputs (unsat).",
                parent=self.root,
            )
            return

        self.status_var.set("Result: SAT - feasible timetable found.")
        assignment: List[Tuple[int, int]] = result["assignment"]  # type: ignore[assignment]
        slots_per_day = result["slots_per_day"]  # type: ignore[assignment]
        schedule_by_slot: Dict[int, List[Tuple[int, int]]] = result[
            "schedule_by_slot"
        ]  # type: ignore[assignment]

        self._populate_assignment_table(assignment, slots_per_day)
        self._populate_slot_view(schedule_by_slot, slots_per_day)

    def _populate_assignment_table(
        self, assignment: List[Tuple[int, int]], slots_per_day: int
    ) -> None:
        """Populate the per-exam table with the latest SAT model."""
        # Replace all existing rows so the table reflects the latest solution.
        self.assignment_tree.delete(*self.assignment_tree.get_children())
        for exam_id, (room_id, slot_id) in enumerate(assignment):
            day = slot_id // slots_per_day
            slot_in_day = slot_id % slots_per_day
            self.assignment_tree.insert(
                "",
                "end",
                values=(exam_id, room_id, slot_id, day, slot_in_day),
            )

    def _populate_slot_view(
        self,
        schedule_by_slot: Dict[int, List[Tuple[int, int]]],
        slots_per_day: int,
    ) -> None:
        """Render the slot-centric tree with per-room listings."""
        # Expand each slot node and list the relevant room assignments.
        self.slot_tree.delete(*self.slot_tree.get_children())
        for slot_id in sorted(schedule_by_slot.keys()):
            day = slot_id // slots_per_day
            slot_in_day = slot_id % slots_per_day
            header = f"Slot {slot_id} - Day {day}, position {slot_in_day}"
            slot_item = self.slot_tree.insert("", "end", text=header)
            for exam_id, room_id in sorted(schedule_by_slot[slot_id]):
                self.slot_tree.insert(
                    slot_item,
                    "end",
                    text="",
                    values=(room_id, exam_id),
                )
            self.slot_tree.item(slot_item, open=True)

    def _clear_output_tables(self) -> None:
        """Remove all rows from both Treeviews."""
        # Used when the solver reports unsatisfiable to blank the GUI panes.
        self.assignment_tree.delete(*self.assignment_tree.get_children())
        self.slot_tree.delete(*self.slot_tree.get_children())

    @staticmethod
    def _read_positive_int(value: str, field_name: str) -> int:
        """Parse and validate a strictly positive integer from the GUI."""
        value = value.strip()
        if not value:
            raise ValueError(f"{field_name} is required.")
        try:
            parsed = int(value)
        except ValueError:
            raise ValueError(f"{field_name} must be an integer.") from None
        if parsed <= 0:
            raise ValueError(f"{field_name} must be greater than 0.")
        return parsed

    @staticmethod
    def _read_non_negative_int(value: str, field_name: str) -> int:
        """Parse and validate an integer that may be zero but not negative."""
        value = value.strip()
        if not value:
            raise ValueError(f"{field_name} is required.")
        try:
            parsed = int(value)
        except ValueError:
            raise ValueError(f"{field_name} must be an integer.") from None
        if parsed < 0:
            raise ValueError(f"{field_name} cannot be negative.")
        return parsed


def main() -> None:
    """Entrypoint so the module can be launched directly."""
    root = tk.Tk()
    ExamSchedulerGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()
