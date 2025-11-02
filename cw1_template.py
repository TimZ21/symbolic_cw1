from z3 import *
from time import perf_counter
from collections import defaultdict
from typing import List, Tuple
import re

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
            # -----------------------------------------------------------------------
            # Just for understanding
            print("match group 0:", match.group(0))
            print("match group 1:", match.group(1))
            # -------------------------------------------------------------------------
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
                instance.exams_to_students.append((int(m.group(1)), int(m.group(2)))) # List of Tuples
            else:
                raise Exception(f'Failed to parse this line: {l}')

    return instance

# Used to solve the basic constraints
# No two exams share the same room at the same slot.
# A room’s capacity is never exceeded.
# No student has two exams at the same slot.
# No student has exams in consecutive slots.

def solve(instance) -> None:
    # Unpack the input, store as constant for security
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    # Basic sanity checks
    # Scuh as the length of the List of romm capaticites should be equal to the number of rooms
    assert len(caps) == R, "room_capacities length must equal number_of_rooms"
    # Make user the exam and student of each pair are in the correct range
    for (e, s) in pairs:
        assert 0 <= e < E, f"exam id {e} out of range(0..{E-1})"
        assert 0 <= s < S, f"student id {s} out of range(0..{S-1})"

    # Build exam to students and student to exams mappings and exam sizes
    # Compute once and resued by onstraints, efficient and clean
    # Who sits exam e
    students_by_exam: List[set] = [set() for _ in range(E)]
    # Which exams student s takes
    exams_by_student: List[set] = [set() for _ in range(S)]
    for e, s in pairs:
        students_by_exam[e].add(s)
        exams_by_student[s].add(e)
    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Decision vars
    # X[e][r][t] is a Boolean: “exam e is placed in room r at slot t”.
    X: List[List[List[BoolRef]]] = [
        [[Bool(f"X_e{e}_r{r}_t{t}") for t in range(T)] for r in range(R)]
        for e in range(E)
    ]

    # Exam e is placed in some room at slot t.
    Y: List[List[BoolRef]] = [
        [Bool(f"Y_e{e}_t{t}") for t in range(T)] for e in range(E)
    ]

    # Ceate the solver
    s = Solver()

    # Helper: exactly one literal true (fallback when Exactly() not available)
    def _exactly_one(lits):
        if not lits:
            s.add(False)  # impossible if there are no rooms/slots
        else:
            s.add(AtMost(*lits, 1))  # ≤ 1
            s.add(Or(lits))          # ≥ 1

    # Link Y with X:  Y[e,t] ↔ OR ( X[e,r,t] for r in range(R) )
    # Reduce the computing time
    for e in range(E):
        for t in range(T):
            s.add(Y[e][t] == Or([X[e][r][t] for r in range(R)]))

    # 1. Exactly one (room, slot) per exam
    for e in range(E):
        lits = [X[e][r][t] for r in range(R) for t in range(T)]
        _exactly_one(lits)

    # 2. At most one exam per (room, slot)
    for r in range(R):
        for t in range(T):
            lits = [X[e][r][t] for e in range(E)]
            s.add(AtMost(*lits, 1))

    # 3. Room capacity respected
    for e in range(E):
        sz = exam_size[e]
        for r in range(R):
            if sz > caps[r]:
                for t in range(T):
                    s.add(Not(X[e][r][t]))

    # 4. No same-slot or consecutive exams for any student
    for s_id in range(S):
        exams = sorted(exams_by_student[s_id])
        for i in range(len(exams)):
            for j in range(i + 1, len(exams)):
                e1, e2 = exams[i], exams[j]
                for t in range(T):
                    s.add(Not(And(Y[e1][t], Y[e2][t])))
                for t in range(T - 1):
                    s.add(Not(And(Y[e1][t],   Y[e2][t + 1])))
                    s.add(Not(And(Y[e1][t + 1], Y[e2][t])))

    # Solve and time the SAT check
    t0 = perf_counter()
    res = s.check()
    t_ms = (perf_counter() - t0) * 1000.0
    print(f"runtime_ms: {t_ms:.3f}")

    if res != sat:
        print("unsat")
        return

    print("sat")
    m = s.model()

    # Extract a concrete (room, slot) for each exam
    assignment: List[Tuple[int, int]] = [(-1, -1) for _ in range(E)]
    for e in range(E):
        found = False
        for r in range(R):
            for t in range(T):
                if is_true(m.evaluate(X[e][r][t], model_completion=True)):
                    assignment[e] = (r, t)
                    found = True
                    break
            if found:
                break
        if not found:
            raise RuntimeError(f"No assignment recovered for exam {e}")

    # Pretty print schedule (one line per exam)
    for e in range(E):
        r, t = assignment[e]
        print(f"exam {e}: room {r}, slot {t}")





if __name__ == '__main__':
    # Read the content from the dict and laod as a solve-acceptable instance "inst"
    inst = read_file('sat1.txt')
    # Solve the instance
    solve(inst)
