# COMP3070 Coursework 1 – Exam Timetabling

This repository contains all artefacts for the COMP3070 Symbolic Artificial Intelligence coursework.  
The goal is to model and solve an exam timetabling problem under a fixed set of “hard” constraints (room capacity, student clashes, per-day limits, turnaround, last-slot bans for large cohorts, and invigilator availability).  
Multiple solver variants are implemented so their behaviour and runtime can be compared both analytically and empirically.

## Input Instance Format

Every solver consumes the same plain-text format:

```
Number of students: <S>
Number of exams: <E>
Number of slots: <T>
Number of rooms: <R>
Room 0 capacity: <int>
Room 1 capacity: <int>
...
<exam_id> <student_id>
<exam_id> <student_id>
```

The header counts declare the basic problem sizes and individual room capacities.  
The remaining lines enumerate `(exam, student)` pairs indicating which students are assigned to which exams. Blank lines are ignored; malformed rows abort with a descriptive error in every solver (and in the GUI).

## Solver Variants

| File | Style | Key Traits |
| --- | --- | --- |
| `cw1_baseline.py` | Quantifier/function Z3 encoding | Mirrors the coursework guide: uses `ExamTime`, `ExamRoom`, and `ExamStudent` uninterpreted functions with extensive `ForAll` constraints. |
| `cw1_boolean.py` | Boolean grid Z3 encoding | Classic `X[e][r][t]` formulation; good propagation thanks to AtMost/Pb constraints. |
| `cw1_int.py` | Integer (time, room) Z3 encoding | Assigns each exam an integer slot and room variable; compact variable set, arithmetic constraints for gaps and per-day limits. |
| `cw1_symmetry.py` | Boolean + symmetry breaking | Extends the Boolean model with additional channelled literals to ensure identical rooms are used in order, reducing search symmetry. |
| `cw1_bayesian.py` | Heuristic Bayesian/annealing search | Constructs full assignments and gradually improves them by minimising weighted violation costs. Fast on SAT, cannot certify UNSAT. |
| `cw1_ortools.py` | OR-Tools CP-SAT | Uses pruned boolean literals, linear constraints, and helper channeling for room usage; benefits from CP-SAT’s presolve and search heuristics. |
| `cw1_gui.py` | Tkinter GUI front-end | Wraps the Boolean solver so users can type instances, tweak constraints (e.g., invigilator capacity), and inspect schedules interactively. |

All Python entry points read the six benchmark files in `test instances/` when run directly; the GUI can either load the same files or accept manual input.

## Runtime Results

Average runtimes (ms) over 10 runs per instance, reproduced from `results.xlsx`:

| Instance | `cw1_baseline.py` | `cw1_int.py` | `cw1_boolean.py` | `cw1_symmetry.py` | `cw1_bayesian.py` | `cw1_ortools.py` |
| --- | --- | --- | --- | --- | --- | --- |
| SAT Short | 13.726 | 1.344 | 0.308 | 0.321 | 0.012 | 12.288 |
| SAT Medium | 35.285 | 3.838 | 5.880 | 6.083 | 0.066 | 24.737 |
| SAT Long | 156.682 | 10.247 | 14.443 | 14.315 | 6.253 | 33.919 |
| UNSAT Short | 3.054 | 1.289 | 0.251 | 0.225 | 0.001 | 0.204 |
| UNSAT Medium | 5.390 | 2.900 | 2.555 | 2.568 | 275.581 | 1.477 |
| UNSAT Long | 81.256 | 76.450 | 75.755 | 75.085 | 1636.852 | 61.188 |

Notes:

1. All Z3-based solvers share the same constraint set and default parameters (`DEFAULT_*` constants).  
2. The Bayesian variant reports “unsat” when it fails to reach zero cost within its annealing budget – it does not deliver a formal proof.  
3. OR-Tools timings include model construction and CP-SAT’s presolve; adjusting solver parameters (seeds, restart policies) can change runtimes slightly.

## Getting Started

1. **Install dependencies**
   ```bash
   # Create / activate a virtual environment first if desired.
   pip install z3-solver ortools protobuf==6.31.1
   ```
   - `z3-solver` powers the Boolean, integer, symmetry, and baseline scripts.  
   - `ortools` provides the CP-SAT engine. Version 9.14 expects `protobuf` < 6.32, hence the pinned 6.31.1 release.  
   - Tkinter ships with standard Python distributions; on Linux install `python3-tk` via your package manager.
2. Ensure Python 3.9+ is available and `pip` installed the above packages without errors.  
3. Run any solver directly, e.g. `python cw1_boolean.py`, to solve all benchmark instances.  
4. Launch the GUI with `python cw1_gui.py` to experiment interactively.

Feel free to plug in new solvers (e.g., MILP, MaxSAT) by following the same input format and reporting conventions. 
