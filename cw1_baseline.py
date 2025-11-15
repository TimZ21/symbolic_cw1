# Quantifier-based encoding derived from the coursework guide.
from z3 import *
from time import perf_counter
from collections import defaultdict
from typing import List, Tuple
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
    # Read one header line like "Number of exams: 12"
    # Extract and return the integer
    def read_attribute(name):
        # Read each line of file
        line = f.readline()
        # Use regex to capture the integer
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception("Could not parse line {line}; expected the {name} attribute")
    
    instance = Instance()
    with open(filename) as f:
        # Load the header counts
        instance.number_of_students = read_attribute("Number of students") # Int
        instance.number_of_exams = read_attribute("Number of exams")       # Int
        instance.number_of_slots = read_attribute("Number of slots")       # Int
        instance.number_of_rooms = read_attribute("Number of rooms")       # Int

        for r in range(instance.number_of_rooms):
            instance.room_capacities.append(read_attribute(f"Room {r} capacity"))   # List of Int

        while True:
            l = f.readline()
            if l == "":
                break
            m = re.match('^\\s*(\\d+)\\s+(\\d+)\\s*$', l)
            if m:
                # Collect (exam, student) pairs
                instance.exams_to_students.append((int(m.group(1)), int(m.group(2))))
            else:
                raise Exception(f'Failed to parse this line: {l}')

    return instance

# Alternative solver: function/quantifier-based encoding

def solve(instance) -> None:
    # Unpack the input, store as constant for security
    E = instance.number_of_exams
    R = instance.number_of_rooms
    T = instance.number_of_slots
    S = instance.number_of_students
    caps: List[int] = list(instance.room_capacities)
    pairs: List[Tuple[int, int]] = list(instance.exams_to_students)

    # Parameters for extra hard constraints
    SLOTS_PER_DAY       = DEFAULT_SLOTS_PER_DAY
    MIN_GAP             = DEFAULT_MIN_GAP
    TURNAROUND_GAP      = DEFAULT_TURNAROUND_GAP
    LARGE_EXAM_THRESHOLD = DEFAULT_LARGE_EXAM_THRESHOLD
    EXAMINER_CAPACITY    = DEFAULT_EXAMINER_CAPACITY

    # Basic sanity checks
    # Scuh as the length of the List of romm capaticites should be equal to the number of rooms
    assert len(caps) == R, "room_capacities length must equal number_of_rooms"
    for (e, s) in pairs:
        assert 0 <= e < E, f"exam id {e} out of range(0..{E-1})"
        assert 0 <= s < S, f"student id {s} out of range(0..{S-1})"

    # Build exam↔student mappings and exam sizes
    students_by_exam: List[set] = [set() for _ in range(E)]
    exams_by_student: List[set] = [set() for _ in range(S)]
    for e, s in pairs:
        students_by_exam[e].add(s)
        exams_by_student[s].add(e)
    exam_size: List[int] = [len(students_by_exam[e]) for e in range(E)]

    # Z3 solver and declarations (function-style encoding)
    s = Solver()

    # Scalar variables (used as bound variables in quantifiers)
    exam    = Int('exam')
    nex     = Int('nex')
    room    = Int('room')
    ts      = Int('ts')
    nts     = Int('nts')
    student = Int('student')

    # Extra bound variables for "at most 2 exams per day" constraint
    exam1, exam2, exam3 = Ints('exam1 exam2 exam3')

    # Range predicates
    Student_Range   = Function('Student_Range',   IntSort(), BoolSort())
    Exam_Range      = Function('Exam_Range',      IntSort(), BoolSort())
    Room_Range      = Function('Room_Range',      IntSort(), BoolSort())
    TimeSlot_Range  = Function('TimeSlot_Range',  IntSort(), BoolSort())

    # Domain definitions
    s.add(ForAll([student],
                 Student_Range(student) ==
                 And(student >= 0, student < S)))
    s.add(ForAll([exam],
                 Exam_Range(exam) ==
                 And(exam >= 0, exam < E)))
    s.add(ForAll([ts],
                 TimeSlot_Range(ts) ==
                 And(ts >= 0, ts < T)))
    s.add(ForAll([room],
                 Room_Range(room) ==
                 And(room >= 0, room < R)))

    # Core functions
    # ExamRoom(e) : which room exam e is in
    # ExamTime(e) : which slot exam e is in
    # ExamStudent(e, s) : does student s sit exam e?
    ExamRoom    = Function('ExamRoom',   IntSort(), IntSort())
    ExamTime    = Function('ExamTime',   IntSort(), IntSort())
    ExamStudent = Function('ExamStudent', IntSort(), IntSort(), BoolSort())

    # Facts: which students take which exams
    for (e, s_id) in pairs:
        s.add(ExamStudent(e, s_id))

    # 1 & 2. Exactly one (room, slot) per exam and
    #        at most one exam per (room, slot)
    #
    # For each exam:
    #   - There exists a room and slot within range
    #   - If any other exam shares that same room & slot, it must be the same exam.
    s.add(
        ForAll(
            [exam],
            Implies(
                Exam_Range(exam),
                Exists(
                    [room, ts],
                    And(
                        Room_Range(room),
                        TimeSlot_Range(ts),
                        ExamTime(exam) == ts,
                        ExamRoom(exam) == room,
                        ForAll(
                            [nex],
                            Implies(
                                Exam_Range(nex),
                                Implies(
                                    And(
                                        ExamRoom(nex) == room,
                                        ExamTime(nex) == ts
                                    ),
                                    exam == nex   # uniqueness
                                )
                            )
                        )
                    )
                )
            )
        )
    )


    # 3. Room capacity respected
    #
    # If ExamRoom(ex2) == rm2, then number of students in ex2
    # must be <= capacity of rm2.
    for ex2 in range(E):
        for rm2 in range(R):
            s.add(
                Implies(
                    ExamRoom(ex2) == rm2,
                    exam_size[ex2] <= caps[rm2]
                )
            )

    # 4 & 5. No same-slot and no consecutive exams for any student
    #
    # For all students, and all pairs of distinct exams they sit:
    #   - if exam has time ts and nex has time nts,
    #     then |ts - nts| must be > MIN_GAP (covers same-slot and close slots).
    s.add(
        ForAll(
            [student, nex, ts, nts, exam],
            Implies(
                And(
                    Student_Range(student),
                    Exam_Range(exam),
                    Exam_Range(nex),
                    TimeSlot_Range(ts),
                    TimeSlot_Range(nts),
                    exam != nex
                ),
                Implies(
                    And(
                        ExamTime(exam) == ts,
                        ExamTime(nex) == nts,
                        ExamStudent(exam, student),
                        ExamStudent(nex, student)
                    ),
                    Abs(ts - nts) > MIN_GAP
                )
            )
        )
    )

    # 6. At most 2 exams per student per day
    # Day(e) = ExamTime(e) // SLOTS_PER_DAY; forbid any student taking 3 exams in one day.
    s.add(
        ForAll(
            [student, exam1, exam2, exam3],
            Implies(
                And(
                    Student_Range(student),
                    Exam_Range(exam1),
                    Exam_Range(exam2),
                    Exam_Range(exam3),
                    exam1 != exam2,
                    exam1 != exam3,
                    exam2 != exam3,
                    ExamStudent(exam1, student),
                    ExamStudent(exam2, student),
                    ExamStudent(exam3, student),
                    ExamTime(exam1) / SLOTS_PER_DAY == ExamTime(exam2) / SLOTS_PER_DAY,
                    ExamTime(exam1) / SLOTS_PER_DAY == ExamTime(exam3) / SLOTS_PER_DAY
                ),
                False  # forbid three exams on the same day for one student
            )
        )
    )

    # 7. Room turnaround: no back-to-back use in the same room (gap >= TURNAROUND_GAP)
    #
    # If two different exams use the same room, their time difference
    # must be > TURNAROUND_GAP (here, at least one empty slot between them).
    s.add(
        ForAll(
            [exam, nex],
            Implies(
                And(
                    Exam_Range(exam),
                    Exam_Range(nex),
                    exam != nex,
                    ExamRoom(exam) == ExamRoom(nex)
                ),
                Abs(ExamTime(exam) - ExamTime(nex)) > TURNAROUND_GAP
            )
        )
    )



    # 8. Large exams not in the last slot of each day
    #
    # Last slot of a day = t such that t % SLOTS_PER_DAY == SLOTS_PER_DAY - 1.
    # For any exam with exam_size[e] >= LARGE_EXAM_THRESHOLD,
    # forbid ExamTime(e) being any such last slot.
    last_slots: List[int] = []
    if SLOTS_PER_DAY > 0:
        for t in range(T):
            if (t % SLOTS_PER_DAY) == SLOTS_PER_DAY - 1:
                last_slots.append(t)

    large_exams = [e for e in range(E) if exam_size[e] >= LARGE_EXAM_THRESHOLD]
    if last_slots and large_exams:
        s.add(
            ForAll(
                [exam],
                Implies(
                    And(
                        Exam_Range(exam),
                        Or([exam == IntVal(e) for e in large_exams])
                    ),
                    And([ExamTime(exam) != t for t in last_slots])
                )
            )
        )

    # 9. limit the number of available invigilators per slot
    examiner_demand = [
        3 if exam_size[e] >= LARGE_EXAM_THRESHOLD else 2
        for e in range(E)
    ]
    if examiner_demand:
        for slot_idx in range(T):
            terms = [
                If(ExamTime(IntVal(e)) == slot_idx, examiner_demand[e], 0)
                for e in range(E)
            ]
            if terms:
                s.add(Sum(terms) <= EXAMINER_CAPACITY)

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

    # Print schedule (one line per exam)
    for ex2 in range(E):
        r_val = m.eval(ExamRoom(ex2))
        t_val = m.eval(ExamTime(ex2))
        print(f"exam {ex2}: room {r_val}, slot {t_val}")


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

