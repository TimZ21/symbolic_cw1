from __future__ import annotations

import math
import random
from time import perf_counter
from typing import List, Tuple, Dict, Set
import re

# Default setting of these parameters
DEFAULT_SLOTS_PER_DAY = 4
DEFAULT_MIN_GAP = 1
DEFAULT_TURNAROUND_GAP = 1
DEFAULT_LARGE_EXAM_THRESHOLD = 10
DEFAULT_EXAMINER_CAPACITY = 10

# Creat the class of instance that could be received by solver
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


def solve(instance: Instance) -> None:
    """
    Bayesian-style (stochastic) solver: constructs a complete assignment and
    uses a Metropolis/annealing search to minimise a weighted violation cost.

    On success (cost == 0), prints a SAT assignment; otherwise prints UNSAT
    with the best assignment found and the runtime.
    """

    # Unpack basic parameters and defaults
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)

    SLOTS_PER_DAY = DEFAULT_SLOTS_PER_DAY
    MIN_GAP = DEFAULT_MIN_GAP
    TURNAROUND_GAP = DEFAULT_TURNAROUND_GAP
    LARGE_EXAM_THRESHOLD = DEFAULT_LARGE_EXAM_THRESHOLD
    EXAMINER_CAPACITY = DEFAULT_EXAMINER_CAPACITY

    # Quick sanity
    if any(x < 0 for x in (E, R, T, S)) or len(caps) != R:
        print("runtime_ms: 0.000")
        print("unsat")
        return
    if E == 0:
        print("runtime_ms: 0.000")
        print("sat")
        return
    if R == 0 or T == 0:
        print("runtime_ms: 0.000")
        print("unsat")
        return

    # Build incidence maps and exam sizes
    students_by_exam: List[Set[int]] = [set() for _ in range(E)]
    exams_by_student: List[Set[int]] = [set() for _ in range(S)]
    for e, s_id in instance.exams_to_students:
        if 0 <= e < E and 0 <= s_id < S:
            students_by_exam[e].add(s_id)
            exams_by_student[s_id].add(e)

    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Precompute day partitions and last-slots per day
    slots_by_day: Dict[int, List[int]] = {}
    for t in range(T):
        d = t // SLOTS_PER_DAY if SLOTS_PER_DAY > 0 else 0
        slots_by_day.setdefault(d, []).append(t)
    last_slots = set()
    if SLOTS_PER_DAY > 0:
        for t in range(T):
            if (t % SLOTS_PER_DAY) == SLOTS_PER_DAY - 1:
                last_slots.add(t)

    # Demand per exam (for invigilator capacity)
    examiner_demand = [3 if exam_size[e] >= LARGE_EXAM_THRESHOLD else 2 for e in range(E)]

    # Feasible (room,slot) candidates per exam (for initialisation and moves)
    candidates: List[List[Tuple[int, int]]] = [[] for _ in range(E)]
    for e in range(E):
        for r in range(R):
            if exam_size[e] > caps[r]:
                continue
            for t in range(T):
                if exam_size[e] >= LARGE_EXAM_THRESHOLD and t in last_slots:
                    continue
                candidates[e].append((r, t))

    # If any exam has no feasible candidate at all, UNSAT under hard rules
    if any(len(candidates[e]) == 0 for e in range(E)):
        print("runtime_ms: 0.000")
        print("unsat")
        return

    # Random initial assignment (greedy random among candidates)
    rng = random.Random(42)
    room_assn: List[int] = [-1] * E
    time_assn: List[int] = [-1] * E
    for e in range(E):
        r, t = rng.choice(candidates[e])
        room_assn[e] = r
        time_assn[e] = t

    # Penalty weights (tuned lightly)
    W_CLASH = 10
    W_MIN_GAP = 6
    W_DAY_CAP = 8
    W_ROOM_DOUBLE = 10
    W_TURNAROUND = 6
    W_LAST_SLOT = 12
    W_INVIG = 8

    def cost(room_a: List[int], time_a: List[int]) -> int:
        total = 0

        # Room double-booking per slot
        occ: Dict[Tuple[int, int], int] = {}
        for e in range(E):
            occ[(room_a[e], time_a[e])] = occ.get((room_a[e], time_a[e]), 0) + 1
        for cnt in occ.values():
            if cnt > 1:
                total += W_ROOM_DOUBLE * (cnt - 1)

        # Student clashes, min-gap, and day-cap
        if S > 0:
            for s_id in range(S):
                exams = list(exams_by_student[s_id])
                if not exams:
                    continue
                # Same-slot and min gap
                for i in range(len(exams)):
                    for j in range(i + 1, len(exams)):
                        t1 = time_a[exams[i]]
                        t2 = time_a[exams[j]]
                        if t1 == t2:
                            total += W_CLASH
                        if abs(t1 - t2) <= MIN_GAP:
                            total += W_MIN_GAP
                # Day cap
                day_counts: Dict[int, int] = {}
                for e in exams:
                    d = time_a[e] // SLOTS_PER_DAY if SLOTS_PER_DAY > 0 else 0
                    day_counts[d] = day_counts.get(d, 0) + 1
                for c in day_counts.values():
                    if c > 2:
                        total += W_DAY_CAP * (c - 2)

        # Turnaround per room
        for r in range(R):
            times = [time_a[e] for e in range(E) if room_a[e] == r]
            times.sort()
            for i in range(1, len(times)):
                if abs(times[i] - times[i - 1]) <= TURNAROUND_GAP:
                    total += W_TURNAROUND

        # Large exams not in last slot
        for e in range(E):
            if exam_size[e] >= LARGE_EXAM_THRESHOLD and time_a[e] in last_slots:
                total += W_LAST_SLOT

        # Invigilator capacity per slot
        for t in range(T):
            demand = 0
            for e in range(E):
                if time_a[e] == t:
                    demand += examiner_demand[e]
            if demand > EXAMINER_CAPACITY:
                total += W_INVIG * (demand - EXAMINER_CAPACITY)

        return total

    # Annealing / Metropolis loop
    t0 = perf_counter()
    best_room = room_assn[:]
    best_time = time_assn[:]
    best_cost = cost(best_room, best_time)

    max_iter = 20000 if E > 0 else 0
    T_start, T_end = 3.0, 0.01

    for it in range(max_iter):
        if best_cost == 0:
            break
        temp = T_start * (T_end / T_start) ** (it / max_iter)
        # Propose: pick an exam and relocate to a random candidate
        e = rng.randrange(E)
        old_r, old_t = room_assn[e], time_assn[e]
        new_r, new_t = rng.choice(candidates[e])
        if (new_r, new_t) == (old_r, old_t):
            continue

        room_assn[e], time_assn[e] = new_r, new_t
        new_cost = cost(room_assn, time_assn)
        # Accept if improves global best, else accept with MH probability against best
        if new_cost < best_cost:
            best_cost = new_cost
            best_room = room_assn[:]
            best_time = time_assn[:]
        else:
            if rng.random() >= math.exp(-(new_cost - best_cost) / max(temp, 1e-6)):
                # revert
                room_assn[e], time_assn[e] = old_r, old_t

    runtime_ms = (perf_counter() - t0) * 1000.0
    print(f"runtime_ms: {runtime_ms:.3f}")

    if best_cost != 0:
        print("unsat")
        return

    print("sat")
    # Emit a concrete schedule
    for e in range(E):
        print(f"exam {e}: room {best_room[e]}, slot {best_time[e]}")


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