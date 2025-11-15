from z3 import *
from time import perf_counter
from collections import defaultdict
from typing import List, Tuple
import re

# Default setting of these parameters, can be set in GUI
DEFAULT_SLOTS_PER_DAY = 4
DEFAULT_MIN_GAP = 1
DEFAULT_TURNAROUND_GAP = 1
DEFAULT_LARGE_EXAM_THRESHOLD = 10
DEFAULT_EXAMINER_CAPACITY = 10

# creat the class of instance that could be received by solver
class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.room_capacities = []
        self.exams_to_students = []

# Read the content from the txt file
def read_file(filename):
    # Red one header line like "Number of exams: 12"
    # Extract and return the integer
    def read_attribute(name):
        # Read each line of file
        line = f.readline()
        # Use regex to caputer the integer
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception("Could not parse line {line}; expected the {name} attribute")
    
    instance = Instance()
    with open(filename) as f:
        # Load the number of each 
        instance.number_of_students = read_attribute("Number of students") # Int
        instance.number_of_exams = read_attribute("Number of exams")    # Int
        instance.number_of_slots = read_attribute("Number of slots")    # Int
        instance.number_of_rooms = read_attribute("Number of rooms")    # Int


        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))   # List of Int

        while True:
            l = f.readline()
            if l == "":
                break
            m = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', l)
            if m:
                instance.exams_to_students.append((int(m.group(1)), int(m.group(2)))) # List of Tuples, exam student list
            else:
                raise Exception(f'Failed to parse this line: {l}')

    return instance

def solve(instance) -> None:
    from ortools.sat.python import cp_model

    # Unpack the problem sizes and clone mutable inputs.
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    # Local copies of the tuning parameters.
    SLOTS_PER_DAY = DEFAULT_SLOTS_PER_DAY
    MIN_GAP = DEFAULT_MIN_GAP
    TURNAROUND_GAP = DEFAULT_TURNAROUND_GAP
    LARGE_EXAM_THRESHOLD = DEFAULT_LARGE_EXAM_THRESHOLD
    EXAMINER_CAPACITY = DEFAULT_EXAMINER_CAPACITY

    # Basic sanity checks on the input data.
    assert len(caps) == R, "room_capacities length must equal number_of_rooms"
    for (e, s) in pairs:
        assert 0 <= e < E, f"exam id {e} out of range(0..{E-1})"
        assert 0 <= s < S, f"student id {s} out of range(0..{S-1})"

    # Build incidence structures and exam sizes.
    students_by_exam: List[set] = [set() for _ in range(E)]
    exams_by_student: List[set] = [set() for _ in range(S)]
    for e, s in pairs:
        students_by_exam[e].add(s)
        exams_by_student[s].add(e)
    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Group slots by day to handle the daily cap.
    slots_by_day: dict[int, List[int]] = defaultdict(list)
    for t in range(T):
        d = t // SLOTS_PER_DAY if SLOTS_PER_DAY > 0 else 0
        slots_by_day[d].append(t)

    # Identify the “last slot of each day” set used by the large-exam rule.
    last_slots = []
    if SLOTS_PER_DAY > 0:
        for t in range(T):
            if (t % SLOTS_PER_DAY) == SLOTS_PER_DAY - 1:
                last_slots.append(t)

    model = cp_model.CpModel()

    X = [[[model.NewBoolVar(f"X_e{e}_r{r}_t{t}") for t in range(T)] for r in range(R)] for e in range(E)]
    Y = [[model.NewBoolVar(f"Y_e{e}_t{t}") for t in range(T)] for e in range(E)]

    for e in range(E):
        for t in range(T):
            room_lits = [X[e][r][t] for r in range(R)]
            if room_lits:
                for lit in room_lits:
                    model.AddImplication(lit, Y[e][t])
                model.AddBoolOr(room_lits + [Y[e][t].Not()])
            else:
                model.Add(Y[e][t] == 0)

    # Exactly-one constraint per exam across all rooms and slots.
    for e in range(E):
        lits = [X[e][r][t] for r in range(R) for t in range(T)]
        if lits:
            model.Add(sum(lits) == 1)
        else:
            model.Add(0 == 1)

    # At most one exam per (room, slot) pair.
    for r in range(R):
        for t in range(T):
            lits = [X[e][r][t] for e in range(E)]
            if len(lits) > 1:
                model.Add(sum(lits) <= 1)

    # Prune placements that exceed the room capacity.
    for e in range(E):
        sz = exam_size[e]
        for r in range(R):
            if sz > caps[r]:
                for t in range(T):
                    model.Add(X[e][r][t] == 0)

    # Student clash and minimum-gap constraints.
    for sid in range(S):
        exams = sorted(exams_by_student[sid])
        for i in range(len(exams)):
            for j in range(i + 1, len(exams)):
                e1, e2 = exams[i], exams[j]
                for t in range(T):
                    model.AddBoolOr([Y[e1][t].Not(), Y[e2][t].Not()])
                for gap in range(1, MIN_GAP + 1):
                    if gap >= T:
                        break
                    for t in range(T - gap):
                        model.AddBoolOr([Y[e1][t].Not(), Y[e2][t + gap].Not()])
                        model.AddBoolOr([Y[e2][t].Not(), Y[e1][t + gap].Not()])

    # At most two exams per student per day.
    for sid in range(S):
        exams = list(exams_by_student[sid])
        if not exams:
            continue
        for day_slots in slots_by_day.values():
            day_lits = [Y[e][t] for e in exams for t in day_slots]
            if len(day_lits) > 2:
                model.Add(sum(day_lits) <= 2)

    # Room turnaround constraint, enforced via helper literals.
    if TURNAROUND_GAP > 0:
        room_used = [[None for _ in range(T)] for _ in range(R)]
        for r in range(R):
            for t in range(T):
                lits = [X[e][r][t] for e in range(E)]
                if not lits:
                    continue
                if len(lits) == 1:
                    room_used[r][t] = lits[0]
                else:
                    aux = model.NewBoolVar(f"RoomUsed_r{r}_t{t}")
                    for lit in lits:
                        model.AddImplication(lit, aux)
                    model.AddBoolOr(lits + [aux.Not()])
                    room_used[r][t] = aux
        for r in range(R):
            for gap in range(1, TURNAROUND_GAP + 1):
                if gap >= T:
                    break
                for t in range(T - gap):
                    lit_now = room_used[r][t]
                    lit_next = room_used[r][t + gap]
                    if lit_now is not None and lit_next is not None:
                        model.AddBoolOr([lit_now.Not(), lit_next.Not()])

    if last_slots:
        for e in range(E):
            if exam_size[e] >= LARGE_EXAM_THRESHOLD:
                for t in last_slots:
                    model.Add(Y[e][t] == 0)

    # Limit the number of invigilators per slot using weighted literals.
    for t in range(T):
        demand_lits = []
        demand_weights = []
        for e in range(E):
            weight = 3 if exam_size[e] >= LARGE_EXAM_THRESHOLD else 2
            for r in range(R):
                demand_lits.append(X[e][r][t])
                demand_weights.append(weight)
        if demand_lits:
            model.Add(sum(lit * w for lit, w in zip(demand_lits, demand_weights)) <= EXAMINER_CAPACITY)

    t0 = perf_counter()
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60.0
    res = solver.Solve(model)
    t_ms = (perf_counter() - t0) * 1000.0
    print(f"runtime_ms: {t_ms:.3f}")

    if res not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        print('unsat')
        return

    print('sat')

    assignment: List[Tuple[int, int]] = [(-1, -1) for _ in range(E)]
    for e in range(E):
        found = False
        for r in range(R):
            for t in range(T):
                if solver.BooleanValue(X[e][r][t]):
                    assignment[e] = (r, t)
                    found = True
                    break
            if found:
                break
        if not found:
            raise RuntimeError(f"No assignment recovered for exam {e}")

    for e in range(E):
        r, t = assignment[e]
        print(f"exam {e}: room {r}, slot {t}")


if __name__ == '__main__':
    # Read three different length sat testing inputs
    sat_short = read_file('sat_short.txt')
    sat_medium = read_file('sat_medium.txt')
    sat_long = read_file('sat_long.txt')

    # Read three different length sat testing inputs
    unsat_short = read_file('unsat_short.txt')
    unsat_medium = read_file('unsat_medium.txt')
    unsat_long = read_file('unsat_long.txt')

    # Solve the instance
    print("sat short: ")
    solve(sat_short)
    print("sat medium: ")
    solve(sat_medium)
    print("sat long: ")
    solve(sat_long)
    print("unsat short: ")
    solve(unsat_short)
    print("unsat medium: ")
    solve(unsat_medium)
    print("unsat long: ")
    solve(unsat_long)
