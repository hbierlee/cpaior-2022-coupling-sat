# Reproducing results for CPAIOR'22 "Coupling Different Integer Encodings for SAT"

To rerun the experiments, jobs are scheduled via `mzn-bench` on a SLURM cluster; so some SLURM configuration with a node is required. In `mzn-bench/schedule.py`, change "critical001" in the code to your node's name.

Build minizinc/open-wbo:

```
cd software/mzn-bench
source bench_env.sh
./build.sh
```

This fetches our PBLib version from a public repository; if the link is dead, the code is available in `./minizinc/pblib-src`.

To run mzn-sat benchmarks, make sure that in the model files, the lines with `include ../sat-declarations.mzn;` are commented before running the model with minizinc-SAT (test) solver/library. Then:

```
./schedule knights
./schedule orienteering
./schedule jsswet slack
./schedule jsswet priority
./schedule table-layout
```

All models and data files are under `./minizinc/tests/benchmarks/mznsat-framework-paper/`. The models are adapted from original problems from the minizinc-benchmarks repository; the original authors are attributed in the model files, and changes (if any) are noted.

To run control solvers:

- Picat-SAT 3.1: included and configured ./minizinc/share/minizinc/solvers/picat-sat.msc
- Chuffed 0.10.4: its .msc files and mznlib have been added and configured, but Chuffed itself must still be installed and fzn-chuffed must be made available on the PATH (or else its path must be added to the .msc file). Its mznlib is slightly modified to enable its native (sub)circuit propagators for improved performance on knights/orienteering.

In the model files, the lines with `include ../sat-declarations.mzn;` must be uncommented before running the model with a control solver. Then:

```
./schedule knights control
./schedule orienteering control
./schedule jsswet slack-control
./schedule jsswet priority-control
./schedule table-layout control
```

The raw data can be aggregrated into statistics and solutions CSV files for further analysis:

```
mzn-bench collect-statistics results/<RESULT>/raw/ results/<RESULT>/stats.csv
mzn-bench collect-objectives results/<RESULT>/raw/ results/<RESULT>/objs.csv
```

Checking for solution and status correctness (because of caching reasons, check-statuses must be (directly!) preceded by check-solutions for the same problem). When checking the jsswet variant, at the start of the file there is some extra data that needs to be uncommented (as indicated by comments), depending on whether you run the 'slack' or 'priority' version of the problem.

```
mzn-bench check-solutions -c 1 --base-dir instances results/<RESULT>/raw/
mzn-bench check-statuses results/<RESULT>/raw/
```

For any questions, feel free to reach out to me at hendrik.bierlee@monash.edu

Kind regards,

Hendrik 'Henk' Bierlee
