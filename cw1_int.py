from z3 import *
from time import perf_counter
from typing import List, Tuple
import re

# Default settings (you can tweak these if needed)
DEFAULT_SLOTS_PER_DAY = 4
DEFAULT_MIN_GAP = 1
DEFAULT_TURNAROUND_GAP = 1
DEFAULT_LARGE_EXAM_THRESHOLD = 10   # exams with >= LARGE_THRESH students can't be in last slot of a day
DEFAULT_EXAMINER_CAPACITY = 10


# Instance container (same structure as your main solver)
class Instance:
    def __init__(self):
        self.number_of_students = 0
        self.number_of_exams = 0
        self.number_of_slots = 0
        self.number_of_rooms = 0
        self.room_capacities: List[int] = []
        self.exams_to_students: List[Tuple[int, int]] = []  # list of (exam, student) pairs


# Parse an instance file (same format as your main solver)
def read_file(filename: str) -> Instance:
    """
    Reads an instance file with header attributes such as:
      Number of students: 3
      Number of exams: 4
      Number of slots: 6
      Number of rooms: 2
      Room 0 capacity: 30
      Room 1 capacity: 30
    followed by lines "e s" meaning "student s sits exam e".
    """

    def read_attribute(name: str) -> int:
        line = f.readline()
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception(f"Could not parse line {line!r}; expected the {name} attribute")

    instance = Instance()
    with open(filename) as f:
        instance.number_of_students = read_attribute("Number of students")
        instance.number_of_exams    = read_attribute("Number of exams")
        instance.number_of_slots    = read_attribute("Number of slots")
        instance.number_of_rooms    = read_attribute("Number of rooms")

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))

        while True:
            l = f.readline()
            if l == "":
                break
            m = re.match(r'^\s*(\d+)\s+(\d+)\s*$', l)
            if m:
                e = int(m.group(1))
                s_id = int(m.group(2))
                instance.exams_to_students.append((e, s_id))
            else:
                raise Exception(f"Failed to parse this line: {l!r}")

    return instance


# Alternative solver: Int-based encoding (time[e], room[e])
def solve(instance: Instance) -> None:
    # Unpack basic parameters
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    # Parameters (you can later expose these via GUI/CLI if you want)
    SLOTS_PER_DAY    = DEFAULT_SLOTS_PER_DAY
    MIN_GAP          = DEFAULT_MIN_GAP
    TURNAROUND_GAP   = DEFAULT_TURNAROUND_GAP
    LARGE_EXAM_THRESHOLD = DEFAULT_LARGE_EXAM_THRESHOLD
    EXAMINER_CAPACITY = DEFAULT_EXAMINER_CAPACITY

    # Basic sanity checks
    assert len(caps) == R, "room_capacities length must equal number_of_rooms"
    for (e, s_id) in pairs:
        assert 0 <= e    < E, f"exam id {e} out of range (0..{E-1})"
        assert 0 <= s_id < S, f"student id {s_id} out of range (0..{S-1})"

    # Build mappings and exam sizes
    students_by_exam: List[set] = [set() for _ in range(E)]
    exams_by_student: List[set] = [set() for _ in range(S)]
    for e, s_id in pairs:
        students_by_exam[e].add(s_id)
        exams_by_student[s_id].add(e)

    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Decision variables: Int time[e], Int room[e]
    s = Solver()

    time = [Int(f"time_{e}") for e in range(E)]  # which slot exam e is in
    room = [Int(f"room_{e}") for e in range(E)]  # which room exam e is in

    for e in range(E):
        s.add(time[e] >= 0, time[e] < T)
        s.add(room[e] >= 0, room[e] < R)

    # 1. Exactly one (room, slot) per exam
    # This is implicit: each exam gets a single time[e] and room[e] via the domains.

    # 2. At most one exam per (room, slot)
    # Distinct exams cannot share the same room and time simultaneously.
    for e1 in range(E):
        for e2 in range(e1 + 1, E):
            s.add(Or(room[e1] != room[e2], time[e1] != time[e2]))

    # 3. Room capacity respected (pruning)
    # If exam_size[e] exceeds the room capacity we forbid room[e] == r.
    for e in range(E):
        sz = exam_size[e]
        for r in range(R):
            if sz > caps[r]:
                s.add(room[e] != r)

    # 4. No same-slot and 5. no consecutive exams for any student
    # For each student we forbid identical slots and gaps <= MIN_GAP.
    for s_id in range(S):
        exams = sorted(exams_by_student[s_id])
        for i in range(len(exams)):
            for j in range(i + 1, len(exams)):
                e1, e2 = exams[i], exams[j]
                s.add(time[e1] != time[e2])
                s.add(Abs(time[e1] - time[e2]) > MIN_GAP)

    # 6. At most 2 exams per student per day
    # Define day(e) = time[e] / SLOTS_PER_DAY (integer division) and limit that count to 2.
    if T > 0 and SLOTS_PER_DAY > 0:
        max_day = (T - 1) // SLOTS_PER_DAY
        for s_id in range(S):
            exams = list(exams_by_student[s_id])
            if not exams:
                continue
            for d in range(max_day + 1):
                count_d = Sum([
                    If(time[e] / SLOTS_PER_DAY == d, 1, 0)
                    for e in exams
                ])
                s.add(count_d <= 2)

    # 7. Room turnaround: no back-to-back use in the same room
    # Same room exams must be separated by more than TURNAROUND_GAP slots.
    if TURNAROUND_GAP > 0:
        for e1 in range(E):
            for e2 in range(e1 + 1, E):
                s.add(
                    Or(
                        room[e1] != room[e2],
                        Abs(time[e1] - time[e2]) > TURNAROUND_GAP
                    )
                )

    # 8. Large exams cannot be scheduled in the last slot of a day
    # Identify last slots in each day and forbid large exams from using them.
    last_slots = []
    if SLOTS_PER_DAY > 0:
        for t in range(T):
            if (t % SLOTS_PER_DAY) == SLOTS_PER_DAY - 1:
                last_slots.append(t)

    for e in range(E):
        if exam_size[e] >= LARGE_EXAM_THRESHOLD:
            for t in last_slots:
                s.add(time[e] != t)

    # 9. Limit the number of available invigilators per slot.
    for t in range(T):
        total_invigilators = Sum([
            If(time[e] == t,
               3 if exam_size[e] >= LARGE_EXAM_THRESHOLD else 2,
               0)
            for e in range(E)
        ])
        s.add(total_invigilators <= EXAMINER_CAPACITY)

    # Solve and time the SAT check
    t0 = perf_counter()
    res = s.check()
    t_ms = (perf_counter() - t0) * 1000.0
    print(f"runtime_ms: {t_ms:.3f}")

    if res != sat:
        print("unsat")
        return

    print("sat")
    model = s.model()

    # Extract room and slot for each exam
    assignment: List[Tuple[int, int]] = [(-1, -1) for _ in range(E)]
    for e in range(E):
        r_val = model.evaluate(room[e], model_completion=True).as_long()
        t_val = model.evaluate(time[e], model_completion=True).as_long()
        assignment[e] = (r_val, t_val)

    # Pretty-print schedule (one line per exam)
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

    inst = read_file('sat3.txt')

    # Solve the instance
    solve(inst)
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
