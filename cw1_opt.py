from z3 import *
from time import perf_counter
from collections import defaultdict
from typing import List, Tuple
import re

# Default setting of these parameters, can be set in GUI
DEFAULT_SLOTS_PER_DAY = 4
DEFAULT_MIN_GAP = 1
DEFAULT_TURNAROUND_GAP = 1
LARGE_THRESH = 10  # or any threshold that makes sense

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

# Used to solve the basic constraints
# No two exams share the same room at the same slot.
# A room’s capacity is never exceeded.
# No student has two exams at the same slot.
# No student has exams in consecutive slots.

def solve(instance) -> None:
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    SLOTS_PER_DAY = DEFAULT_SLOTS_PER_DAY
    MIN_GAP = DEFAULT_MIN_GAP
    TURNAROUND_GAP = DEFAULT_TURNAROUND_GAP

    assert len(caps) == R, "room_capacities length must equal number_of_rooms"
    for (e, s) in pairs:
        assert 0 <= e < E, f"exam id {e} out of range(0..{E-1})"
        assert 0 <= s < S, f"student id {s} out of range(0..{S-1})"

    if E == 0:
        print("runtime_ms: 0.000")
        print("sat")
        return
    if R == 0 or T == 0:
        print("unsat")
        return

    students_by_exam: List[set] = [set() for _ in range(E)]
    exams_by_student: List[set] = [set() for _ in range(S)]
    for e, s in pairs:
        students_by_exam[e].add(s)
        exams_by_student[s].add(e)
    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    if SLOTS_PER_DAY > 0:
        slots_by_day: dict[int, List[int]] = defaultdict(list)
        for t in range(T):
            slots_by_day[t // SLOTS_PER_DAY].append(t)
    else:
        slots_by_day = {0: list(range(T))}

    last_slots = set()
    if SLOTS_PER_DAY > 0:
        last_slots = {t for t in range(T) if (t % SLOTS_PER_DAY) == SLOTS_PER_DAY - 1}

    s = Solver()

    X: List[List[List[BoolRef]]] = [
        [[None for _ in range(T)] for _ in range(R)]
        for _ in range(E)
    ]
    per_exam_lits: List[List[BoolRef]] = [[] for _ in range(E)]
    room_slot_lits: List[List[List[BoolRef]]] = [[[] for _ in range(T)] for _ in range(R)]
    exam_slot_lits: List[List[List[BoolRef]]] = [[[] for _ in range(T)] for _ in range(E)]

    for e in range(E):
        feasible_rooms = [r for r in range(R) if exam_size[e] <= caps[r]]
        if not feasible_rooms:
            print("unsat")
            return
        for r in feasible_rooms:
            for t in range(T):
                if exam_size[e] >= LARGE_THRESH and t in last_slots:
                    continue
                var = Bool(f"X_e{e}_r{r}_t{t}")
                X[e][r][t] = var
                per_exam_lits[e].append(var)
                room_slot_lits[r][t].append(var)
                exam_slot_lits[e][t].append(var)

    slot_occ: List[List[BoolRef]] = [[None for _ in range(T)] for _ in range(E)]
    for e in range(E):
        for t in range(T):
            bucket = exam_slot_lits[e][t]
            if not bucket:
                continue
            slot_occ[e][t] = Or(bucket) if len(bucket) > 1 else bucket[0]

    room_use: List[List[BoolRef]] = [[None for _ in range(T)] for _ in range(R)]
    for r in range(R):
        for t in range(T):
            bucket = room_slot_lits[r][t]
            if not bucket:
                continue
            room_use[r][t] = Or(bucket) if len(bucket) > 1 else bucket[0]

    for lits in per_exam_lits:
        if not lits:
            print("unsat")
            return
        if len(lits) == 1:
            s.add(lits[0])
        else:
            s.add(PbEq([(lit, 1) for lit in lits], 1))

    for r in range(R):
        for t in range(T):
            lits = room_slot_lits[r][t]
            if len(lits) > 1:
                s.add(PbLe([(lit, 1) for lit in lits], 1))

    for sid in range(S):
        exams = sorted(exams_by_student[sid])
        for i in range(len(exams)):
            for j in range(i + 1, len(exams)):
                e1, e2 = exams[i], exams[j]
                for t in range(T):
                    lit1 = slot_occ[e1][t]
                    lit2 = slot_occ[e2][t]
                    if lit1 is not None and lit2 is not None:
                        s.add(Not(And(lit1, lit2)))
                for gap in range(1, MIN_GAP + 1):
                    if gap >= T:
                        break
                    for t in range(T - gap):
                        lit_a = slot_occ[e1][t]
                        lit_b = slot_occ[e2][t + gap]
                        if lit_a is not None and lit_b is not None:
                            s.add(Not(And(lit_a, lit_b)))
                        lit_c = slot_occ[e2][t]
                        lit_d = slot_occ[e1][t + gap]
                        if lit_c is not None and lit_d is not None:
                            s.add(Not(And(lit_c, lit_d)))

    for sid in range(S):
        exams = list(exams_by_student[sid])
        if not exams:
            continue
        for day_slots in slots_by_day.values():
            day_lits: List[BoolRef] = []
            for e in exams:
                for t in day_slots:
                    lit = slot_occ[e][t]
                    if lit is not None:
                        day_lits.append(lit)
            if len(day_lits) > 2:
                s.add(PbLe([(lit, 1) for lit in day_lits], 2))

    if TURNAROUND_GAP > 0:
        for r in range(R):
            for gap in range(1, TURNAROUND_GAP + 1):
                if gap >= T:
                    break
                for t in range(T - gap):
                    lit_now = room_use[r][t]
                    lit_next = room_use[r][t + gap]
                    if lit_now is not None and lit_next is not None:
                        s.add(Not(And(lit_now, lit_next)))

    t0 = perf_counter()
    res = s.check()
    t_ms = (perf_counter() - t0) * 1000.0
    print(f"runtime_ms: {t_ms:.3f}")

    if res != sat:
        print("unsat")
        return

    print("sat")
    m = s.model()

    assignment: List[Tuple[int, int]] = [(-1, -1) for _ in range(E)]
    for e in range(E):
        found = False
        for r in range(R):
            for t in range(T):
                lit = X[e][r][t]
                if lit is None:
                    continue
                if is_true(m.evaluate(lit, model_completion=True)):
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