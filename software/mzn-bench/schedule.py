#!/usr/bin/env python

from pprint import pprint
import logging
import enum
from datetime import date, timedelta
from pathlib import Path
import sys
import platform
import minizinc
logging.basicConfig(filename="/tmp/minizinc-python.log", level=logging.DEBUG)

PB_ENCODERS=[ "PB_BEST", "PB_BDD", "PB_SWC", "PB_SORTINGNETWORKS", "PB_ADDER", "PB_BINARY_MERGE" ]
OPEN_WBO_ALGORITHMS={
        0: "wbo",
        1: "linear-su",
        2: "msu3",
        3: "part-msu3",
        4: "oll",
        5: "best",
        }
LOANDRA_ALGORITHMS={
        0: "core-guided",
        1: "core-boosted",
        2: "only-linear-search",
        }

model_extra_data={}

from mzn_bench import Configuration, schedule
# solver_time_limit=1000*60*10
solver_time_limit=1000*60*10
flat_time_limit=1000*60*10
def encoding_name(encoding):
    if encoding == 'SAT_DEFAULT':
        return "mixed"
    elif encoding == 'SAT_UNARY':
        return "direct"
    elif encoding == 'SAT_ORDER':
        return "order"
    elif encoding == 'SAT_BINARY':
        return "binary"
    else:
        raise RunTimeError("err")

def sat_config(name=None, solver="lingeling", encoding=None, opt=False, extra_data={}, other_flags={}):
    # if encoding is not None:
    #     encoding_setting_data["fSAT_encoding_mode"] = minizinc.model.UnknownExpression(encoding);
    #     # extra_data["fSAT_encoding_mode"] = enum.Enum("SAT_Encoding", encoding)(1);

    if name is None:
        name=f"mzn-sat-{extra_data}-{solver}"

    if encoding:
        extra_data["fSAT_encoding_mode"]=minizinc.model.UnknownExpression(encoding)

    return {
            # "name": f"mzn-sat-{enc_name}-{sat_solver}{'-o3' if opt else ''}",
            "name": name,
            "solver": minizinc.Solver.lookup(solver),
            "other_flags": {
                "intermediate-solutions": True,
                # "solver-time-limit": 1000*60*1, # ms*s*m
                **other_flags,
                },
            "extra_data": {
                "fSATVerbosity": 0,
                **extra_data,
                }
            }

def get_configurations(key, instances, mzn_path, run_name):
    other_flags={'solver-time-limit': solver_time_limit}
    if key == "jsswet":
        if "priority" in run_name:
            model_extra_data={
                "f_fixed_horizon": False,
                "f_high_priority_penalty": 30,
                "f_high_priority_hard_deadline": 500,
                }
        elif "slack" in run_name:
            model_extra_data={
                "f_use_fixed_horizon": True,
                "f_quick_finish_slack": 2.5,
                }


        if "control" in run_name:
            return [
                    Configuration(name="picat_sat", solver=minizinc.Solver.lookup("picat-sat"), free_search=True, extra_data={"f_use_globals": True, "f_is_picat_sat": True, **model_extra_data}),
                    Configuration(name="picat_sat-dump", solver=minizinc.Solver.lookup("picat-sat-dump"), free_search=True, extra_data={"f_use_globals": True, **model_extra_data}),
                    Configuration(name="chuffed", solver=minizinc.Solver.lookup("chuffed"), free_search=True, extra_data={"f_use_globals": True, **model_extra_data}),
                    Configuration(name="gecode", solver=minizinc.Solver.lookup("gecode"), free_search=True, extra_data={"f_use_globals": True, **model_extra_data}),
                    ]
        return [
                Configuration(
                    **sat_config(
                        name=f"mzn_sat-{solver.replace('-','_')}-{encoding_name(encoding)}{f'-{opt}' if len(opt)>0 else ''}",
                        solver=solver,
                        encoding=encoding,
                        other_flags=other_flags,
                        extra_data={**model_extra_data, **opt}
                        ),
                    minizinc=mzn_path,
                    )
                for solver in [
                   "open-wbo",
                    #"loandra",
                   ]
                for encoding in [
                    'SAT_DEFAULT',
                    # 'SAT_UNARY',
                    'SAT_ORDER',
                    'SAT_BINARY',
                    ]
                for opt in (
                    [{}] if "priority" in run_name else (
                        [{"f_SAT_fzn_disjunctive_order_alternative": True}] if encoding == "SAT_ORDER" else
                        ([{"f_SAT_fzn_disjunctive_order_alternative": True, "f_slack_channel": slack} for slack in ["EQUALITY", "INEQUALITY", "DOUBLE_INEQUALITY" ] ] if encoding == "SAT_DEFAULT" else [{}])
                        )
                    )
                ]
    elif key in {"knights","orienteering"}:
        if run_name is not None and "control" in run_name:
            return [
                    Configuration(name="picat_sat", solver=minizinc.Solver.lookup("picat-sat"), free_search=True, extra_data=model_extra_data),
                    Configuration(name="picat_sat-dump", solver=minizinc.Solver.lookup("picat-sat-dump"), free_search=True, extra_data=model_extra_data),
                    Configuration(name="chuffed", solver=minizinc.Solver.lookup("chuffed"), other_flags={}, free_search=True, extra_data=model_extra_data),
                    ]
        return [
                Configuration(
                    **sat_config(
                    name=f"mzn-sat-{solver}"+
                       f"-{'direct' if encoding == 'SAT_DEFAULT' else encoding_name(encoding)}"
                               +f"{'+order' if allow_redundant_encodings else ''}"
                           +f"-{encoding_name(circuit_encoding) if encoding == 'SAT_DEFAULT' else encoding_name(encoding)}"
                           +f"{(('-'+(encoding_name(distances_encoding))) if encoding == 'SAT_DEFAULT' else ('-'+encoding_name(encoding))) if key == 'orienteering' else ''}"
                           ,
                    solver=solver,
                    other_flags=other_flags,
                    extra_data={
                "fSAT_encoding_mode": minizinc.model.UnknownExpression(encoding),
                "fSAT_allow_redundant_encodings": allow_redundant_encodings,
                "f_SAT_overrule_pbify": False,
                "fSAT_circuit_order_var_encoding": minizinc.model.UnknownExpression(circuit_encoding or "SAT_ORDER"),
                "fSAT_array_int_element_result_encoding": minizinc.model.UnknownExpression(distances_encoding or "SAT_ORDER"),
                }))
                for encoding in ([
                    'SAT_DEFAULT',
                    'SAT_UNARY',
                    'SAT_ORDER',
                    'SAT_BINARY',
                    ] if key == 'knight' else ['SAT_DEFAULT'])
                for circuit_encoding in ([ 'SAT_UNARY', 'SAT_ORDER', 'SAT_BINARY' ] if encoding == 'SAT_DEFAULT' and key == 'knights' else [ 'SAT_ORDER' ])
                for allow_redundant_encodings in ([True, False] if encoding == 'SAT_DEFAULT' and key == 'knights' else [ False ])
                for distances_encoding in (['SAT_UNARY',  'SAT_ORDER', 'SAT_BINARY'] if key == "orienteering" and encoding == 'SAT_DEFAULT' else [ None ])
                for solver in [ 'open-wbo' ]
                ]
        return [
                Configuration(
                    **sat_config(
                    name=f"mzn-sat-{solver}"+
                       f"-{'direct' if encoding == 'SAT_DEFAULT' else encoding_name(encoding)}"
                               +f"{'+order' if allow_redundant_encodings else ''}"
                           +f"-{encoding_name(circuit_encoding) if encoding == 'SAT_DEFAULT' else encoding_name(encoding)}"
                           +f"{(('-'+(encoding_name(distances_encoding))) if encoding == 'SAT_DEFAULT' else ('-'+encoding_name(encoding))) if key == 'orienteering' else ''}"
                           ,
                    solver=solver,
                    other_flags=other_flags,
                    extra_data={
                "fSAT_encoding_mode": minizinc.model.UnknownExpression(encoding),
                "fSAT_allow_redundant_encodings": allow_redundant_encodings,
                "fSAT_circuit_order_var_encoding": minizinc.model.UnknownExpression(circuit_encoding or "SAT_BINARY"),
                "fSAT_array_int_element_result_encoding": minizinc.model.UnknownExpression(distances_encoding or "SAT_ORDER"),
                }))
                for encoding in [
                    'SAT_DEFAULT',
                    'SAT_UNARY',
                    'SAT_ORDER',
                    'SAT_BINARY',
                    ]
                for circuit_encoding in ([ 'SAT_UNARY', 'SAT_ORDER', 'SAT_BINARY' ] if encoding == 'SAT_DEFAULT' else [ None ])
                for allow_redundant_encodings in ([True, False] if encoding == 'SAT_DEFAULT' else [ False ])
                for distances_encoding in (['SAT_BINARY', 'SAT_ORDER'] if key == "orienteering" and encoding == 'SAT_DEFAULT' else [ None ])
                for solver in [ 'open-wbo' ]
                ]
    elif key == "tablelayout":
        def extra_other_flags(solver, open_wbo_algorithm, loandra_algorithm):
            if solver == 'open-wbo' and open_wbo_algorithm >= 0:
                return {'extra-solver-args': f"-algorithm={open_wbo_algorithm}"}
            elif solver == 'loandra' and loandra_algorithm >= 0:
                return {'extra-solver-args': f"-pmreslin={loandra_algorithm}"}
            else:
                return {}
 
        open_wbo_algorithm=5
        loandra_algorithm=1
        model_extra_data={}

        if control in run_name:
            return [
                    Configuration(name="picat_sat", solver=minizinc.Solver.lookup("picat-sat"), free_search=True, extra_data=model_extra_data),
                    Configuration(name="picat_sat-dump", solver=minizinc.Solver.lookup("picat-sat-dump"), free_search=True, extra_data=model_extra_data),
                    Configuration(name="chuffed", solver=minizinc.Solver.lookup("chuffed"), other_flags={}, free_search=False, extra_data=model_extra_data),
                    ]

        return [
                Configuration(
                    **sat_config(
                    name=f"mzn-sat-{solver}"
                       +f"-{f_mzn_sat_test}"
                       +f"-{f_SAT_domain_aware_enc}"
                       +f"-{f_SAT_pb_encoder}"
                       +(f"-{OPEN_WBO_ALGORITHMS[open_wbo_algorithm]}" if (solver=='open-wbo' and open_wbo_algorithm>=0) else f"-{LOANDRA_ALGORITHMS[loandra_algorithm]}")
                           ,
                    solver=solver,
                    other_flags={
                        **other_flags,
                        **extra_other_flags(solver, open_wbo_algorithm, loandra_algorithm)
                        },
                    extra_data={
                "fSAT_encoding_mode": "SAT_DEFAULT",
                "f_mzn_sat_test": f_mzn_sat_test,
                "f_SAT_domain_aware_enc": f_SAT_domain_aware_enc,
                "f_SAT_pb_encoder": f_SAT_pb_encoder,
                "fSAT_array_int_element_method": "GROUPWISE", 
                **model_extra_data,
                }))
                for f_mzn_sat_test in [
                    "order_binary_binary", # compact ; only coupling; can't use msu3
                    "order_binary_order", # only coupling, but order objective ; can use msu3
                    "order_orderBinary_order", # same but with channelling ; objective still order
                    ]
                for f_SAT_domain_aware_enc in [ True ]
                for f_SAT_pb_encoder in [ "PB_BEST" ]
                for solver in [ 'open-wbo' ]
                for open_wbo_algorithm in ([5] if f_mzn_sat_test == "order_binary_binary" else [5,3])
                ]

def main():
    args=iter(sys.argv)
    next(args) # skip argv[0] ./schedule.py
    instances=next(args)
    run_name=next(args, None)

    if platform.node() == "air":
        nodelist=["air"]
        mzn_path="/home/hbierlee/Projects/libminizinc/release/minizinc"
        minizinc.CLI.CLIDriver(Path(mzn_path)).make_default()
        memory=1024
        timeout=timedelta(minutes=1)
    else:
        nodelist=["critical001"]
        memory=round(1024*10)
        mzn_path="/home/hbierlee/Projects/libminizinc/release/minizinc"
        timeout=timedelta(milliseconds=flat_time_limit+solver_time_limit)
        if run_name is not None and "control" in run_name:
            timeout=timedelta(milliseconds=solver_time_limit)

    if instances in {"mznc2020", "mznc2021", "mznc2019"}:
        configurations = get_configurations("half_reifications", instances, mzn_path, run_name)
    elif instances in {"peaceable_queens"}:
        mzn_path="/opt/easybuild/software/MiniZinc/2.5.5/bin/minizinc"
        minizinc.CLI.CLIDriver(Path(mzn_path)).make_default()
        configurations = get_configurations("peaceable_queens", instances, mzn_path, run_name)
    elif "jsswet" in instances:
        configurations = get_configurations("jsswet", instances, mzn_path, run_name)
    elif "knights" in instances:
        configurations = get_configurations("knights", instances, mzn_path, run_name)
    elif "orienteering" in instances:
        configurations = get_configurations("orienteering", instances, mzn_path, run_name)
    elif "table-layout" in instances:
        configurations = get_configurations("tablelayout", instances, mzn_path, run_name)
    elif "paper" in instances:
        configurations = get_configurations("paper", instances, mzn_path, run_name)
    else:
        assert False, "unknown instances {instances}"

    model_extra_data_str=str(model_extra_data).replace(' ','').replace('\'','').replace('{','').replace('}','').replace(':','-').replace(',','-').lower()
    run=f"{str(date.today())}-{instances}{f'-{run_name}' if run_name is not None else ''}{'-'+model_extra_data_str if model_extra_data_str != '' else ''}{'-'+('_'.join(nodelist) if nodelist[0] != 'critical001' else '')}"
    pprint(sorted([c.name for c in configurations]))
    output_dir=f"./results/{run}/raw"



    schedule(
            debug=True,
            instances=Path(f"./instances/{instances}.csv"),
            memory=memory,
            timeout=timeout,
            output_dir=Path(output_dir),
            configurations=configurations,
            nodelist=nodelist,
            )

if __name__ == "__main__":
    main()

