from z3 import *
from time import perf_counter
from collections import defaultdict
from typing import List, Tuple

from cw1_boolean import (
    Instance,
    read_file,
    DEFAULT_SLOTS_PER_DAY,
    DEFAULT_MIN_GAP,
    DEFAULT_TURNAROUND_GAP,
    DEFAULT_LARGE_EXAM_THRESHOLD,
    DEFAULT_EXAMINER_CAPACITY,
)


def solve(instance: Instance) -> None:
    # Unpack problem sizes
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    # Parameters
    SLOTS_PER_DAY = DEFAULT_SLOTS_PER_DAY
    MIN_GAP = DEFAULT_MIN_GAP
    TURNAROUND_GAP = DEFAULT_TURNAROUND_GAP
    LARGE_EXAM_THRESHOLD = DEFAULT_LARGE_EXAM_THRESHOLD
    EXAMINER_CAPACITY = DEFAULT_EXAMINER_CAPACITY

    # Sanity checks
    if len(caps) != R:
        raise ValueError("room_capacities length must equal number_of_rooms")
    for (e, s_id) in pairs:
        if not (0 <= e < E):
            raise ValueError(f"exam id {e} out of range")
        if not (0 <= s_id < S):
            raise ValueError(f"student id {s_id} out of range")

    if E == 0:
        print("runtime_ms: 0.000")
        print("sat")
        return

    # Incidence maps
    students_by_exam: List[set] = [set() for _ in range(E)]
    exams_by_student: List[set] = [set() for _ in range(S)]
    for e, s_id in pairs:
        students_by_exam[e].add(s_id)
        exams_by_student[s_id].add(e)
    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Decision vars
    solver = Solver()
    X: List[List[List[BoolRef]]] = [
        [[Bool(f"X_e{e}_r{r}_t{t}") for t in range(T)] for r in range(R)]
        for e in range(E)
    ]
    Y: List[List[BoolRef]] = [
        [Bool(f"Y_e{e}_t{t}") for t in range(T)]
        for e in range(E)
    ]

    # Slots per day partitions
    slots_by_day: defaultdict[int, List[int]] = defaultdict(list)
    for t in range(T):
        slots_by_day[t // SLOTS_PER_DAY if SLOTS_PER_DAY > 0 else 0].append(t)

    # Link Y with X
    for e in range(E):
        for t in range(T):
            solver.add(Y[e][t] == Or([X[e][r][t] for r in range(R)]))

    # Exactly one (room, slot) per exam
    for e in range(E):
        lits = [X[e][r][t] for r in range(R) for t in range(T)]
        if lits:
            solver.add(AtMost(*lits, 1))
            solver.add(Or(lits))
        else:
            solver.add(False)

    # At most one exam per (room, slot)
    for r in range(R):
        for t in range(T):
            lits = [X[e][r][t] for e in range(E)]
            if len(lits) > 1:
                solver.add(AtMost(*lits, 1))

    # Room capacity pruning
    for e in range(E):
        sz = exam_size[e]
        for r in range(R):
            if sz > caps[r]:
                for t in range(T):
                    solver.add(Not(X[e][r][t]))

    # Student constraints (no same slot, min gap)
    for s_id in range(S):
        exams = sorted(exams_by_student[s_id])
        for i in range(len(exams)):
            for j in range(i + 1, len(exams)):
                e1, e2 = exams[i], exams[j]
                for t in range(T):
                    solver.add(Not(And(Y[e1][t], Y[e2][t])))
                for gap in range(1, MIN_GAP + 1):
                    for t in range(T - gap):
                        solver.add(Not(And(Y[e1][t], Y[e2][t + gap])))
                        solver.add(Not(And(Y[e1][t + gap], Y[e2][t])))

    # Two exams per day per student
    for s_id in range(S):
        exams = list(exams_by_student[s_id])
        for day_slots in slots_by_day.values():
            day_lits = [Y[e][t] for e in exams for t in day_slots]
            if day_lits:
                solver.add(AtMost(*day_lits, 2))

    # Room turnaround
    if TURNAROUND_GAP > 0:
        for r in range(R):
            for gap in range(1, TURNAROUND_GAP + 1):
                for t in range(T - gap):
                    used_now = Or([X[e][r][t] for e in range(E)])
                    used_next = Or([X[e][r][t + gap] for e in range(E)])
                    solver.add(Not(And(used_now, used_next)))

    # Last slot restriction for large exams
    last_slots = [t for t in range(T) if SLOTS_PER_DAY > 0 and (t % SLOTS_PER_DAY) == SLOTS_PER_DAY - 1]
    for e in range(E):
        if exam_size[e] >= LARGE_EXAM_THRESHOLD:
            for t in last_slots:
                solver.add(Not(Y[e][t]))

    # Invigilator capacity per slot
    examiner_demand = [3 if exam_size[e] >= LARGE_EXAM_THRESHOLD else 2 for e in range(E)]
    for t in range(T):
        demand_terms = []
        for e in range(E):
            for r in range(R):
                demand_terms.append((X[e][r][t], examiner_demand[e]))
        if demand_terms:
            solver.add(PbLe(demand_terms, EXAMINER_CAPACITY))

    # Symmetry-breaking: enforce that identical rooms are used in ascending order.
    room_used = [[Bool(f"used_r{r}_t{t}") for t in range(T)] for r in range(R)]
    for r in range(R):
        for t in range(T):
            lits = [X[e][r][t] for e in range(E)]
            if lits:
                solver.add(room_used[r][t] == Or(lits))
            else:
                solver.add(Not(room_used[r][t]))

    for r in range(1, R):
        if caps[r] == caps[r - 1]:
            for t in range(T):
                earlier = room_used[r - 1][: t + 1]
                if earlier:
                    solver.add(Implies(room_used[r][t], Or(earlier)))
                else:
                    solver.add(Not(room_used[r][t]))

    # Solve
    t0 = perf_counter()
    res = solver.check()
    t_ms = (perf_counter() - t0) * 1000.0
    print(f"runtime_ms: {t_ms:.3f}")

    if res != sat:
        print("unsat")
        return

    print("sat")
    model = solver.model()

    assignment: List[Tuple[int, int]] = [(-1, -1) for _ in range(E)]
    for e in range(E):
        for r in range(R):
            for t in range(T):
                if is_true(model.evaluate(X[e][r][t], model_completion=True)):
                    assignment[e] = (r, t)
                    break
            if assignment[e][0] != -1:
                break

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