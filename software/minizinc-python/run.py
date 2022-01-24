import logging
logging.basicConfig(filename="minizinc-python.log", level=logging.DEBUG)

import minizinc


# {
#         # "name": f"mzn-sat-{encoding.lower() if encoding is not None else 'default'}-{sat_solver}{'-pblib' if pblib else ''}{'-o3' if opt else ''}",
#         "name": f"mzn-sat-{encoding.lower() if encoding is not None else 'default'}-{sat_solver}{'-o3' if opt else ''}",
#         "solver": minizinc.Solver.lookup("org.minizinc.mzn-sat"),
#         "other_flags": {"solver-input-format": "dimacs-wcnf", "intermediate-solutions-x": True, "sat-cmd": sat_solver, "output-detailed-timing": True},
#         "extra_data": extra_data,
#         }

model = minizinc.Model("/home/hbierlee/Projects/minizinc-slurm/mznc2019/rotating-workforce/rotating-workforce.mzn")
# model = minizinc.Model("/home/hbierlee/Projects/libminizinc/tests/spec/unit/globals/roots/test_roots3.mzn")

# model.add_string("n=4")

# model = minizinc.Model()
# model.add_string(
#     """
#     include "all_different.mzn";
#     array[1..5] of var 1..5: arr;
#     constraint all_different(arr);
#     """
# )

# solver = minizinc.Solver.lookup("gecode")
# instance = minizinc.Instance(solver, model)
# result = instance.solve()


solver = minizinc.Solver.lookup("mzn-sat")
instance = minizinc.Instance(solver, model)
instance.add_file("/home/hbierlee/Projects/minizinc-slurm/mznc2019/rotating-workforce/Example1242.dzn", parse_data=False)
instance["fSAT_encoding_mode"] = minizinc.model.UnknownExpression("SAT_BINARY");

with instance.files() as files:
    print("files", files)
    for f in files:
        with open(f) as f_i:
            print("f", f_i.read())

result = instance.solve(**{"solver-input-format": "dimacs-wcnf", "sat-cmd": "loandra"})

print('r', result)

