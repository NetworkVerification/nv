#!/usr/bin/env python3
"""
Main module to generate, run and tabulate the Kirigami benchmarks.
"""

import argparse
import os
import re
from datetime import datetime
from gen_part_nv import gen_part_nv, run_nv_simulate
from tabulate_sp_bench import (
    run_trials_sync,
    run_trials_parallel,
    write_csv,
    DISTINCT_OPERATIONS,
)

BENCH_DIR = "benchmarks/SinglePrefix"


def get_benchmarks():
    """Return the list of input benchmark files with their destinations."""
    common = [(4, 10), (8, 12), (10, 13), (12, 64), (16, 0), (20, 0)]
    # benches = [
    #         (f"{BENCH_DIR}/FAT{sz}/sp{sz}.nv", d) for (sz, d) in common
    # ]
    benches = [(f"{BENCH_DIR}/FAT{sz}/fat{sz}Pol.nv", d) for (sz, d) in common]
    return benches


def simulate_benchmarks(benchmarks):
    """
    Simulate the given benchmarks and collect the results of simulation.
    """
    all_solutions = dict()
    for (inputf, _) in benchmarks:
        solutions = run_nv_simulate(inputf)
        all_solutions[inputf] = solutions
    return all_solutions


def create_benchmarks(benchmarks):
    """
    Generate the necessary benchmarks to use.
    """
    for (inputf, dest) in benchmarks:
        gen_part_nv(inputf, dest, "h")
        gen_part_nv(inputf, dest, "v")
        gen_part_nv(inputf, dest, "pods")


def clean_benchmarks(dry_run):
    """Remove old benchmarks."""
    # pat = re.compile(r"^sp\d*-(part|vpart|pods)\d*\.nv$", re.M)
    pat = re.compile(r"^fat\d*Pol-(h|v|p)\d*\.nv$", re.M)
    for root, _, files in os.walk(BENCH_DIR):
        for fname in files:
            if pat.search(fname):
                bench_path = os.path.join(root, fname)
                if dry_run:
                    print(f"Removing {bench_path}")
                else:
                    os.remove(bench_path)


def save_results(runs):
    """Save runs to CSV."""
    timestamp = datetime.now()
    time = timestamp.strftime("%Y-%m-%d-%H:%M:%S")
    return write_csv(runs, f"kirigami-results-{time}.csv")


def tabulate_fattree_benchmarks(
    sizes, timeout=3600, trials=10, save_progress=True, parallel=False
):
    """
    Run all the vertical and horizontal benchmarks.
    """
    runs = []
    for size in sizes:
        directory = f"{BENCH_DIR}/FAT{size}"
        # benches = [
        #     (None, f"sp{size}.nv"),
        #     ("horizontal", f"sp{size}-part.nv"),
        #     ("vertical", f"sp{size}-vpart.nv"),
        #     ("pods", f"sp{size}-pods.nv"),
        # ]
        benches = [
            (None, f"fat{size}Pol.nv"),
            ("horizontal", f"fat{size}Pol-h.nv"),
            ("vertical", f"fat{size}Pol-v.nv"),
            ("pods", f"fat{size}Pol-pods.nv"),
        ]
        if parallel:
            fn = run_trials_parallel
        else:
            fn = run_trials_sync
        results = fn(directory, benches, timeout, trials, DISTINCT_OPERATIONS)
        runs.append(results)
        if save_progress:
            save_results(runs)
    return runs


OPERATIONS = [
    "make",
    "clean",
    "list",
    "run",
    "sim",
]

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Frontend for benchmarking the Kirigami tool."
    )
    parser.add_argument("op", type=str, choices=OPERATIONS, help="operation to run")
    parser.add_argument("sizes", type=int, nargs="*")
    args = parser.parse_args()
    if args.op == "make":
        create_benchmarks(get_benchmarks())
    if args.op == "clean":
        clean_benchmarks(dry_run=False)
    if args.op == "list":
        clean_benchmarks(dry_run=True)
    if args.op == "run":
        save_results(tabulate_fattree_benchmarks(args.sizes, parallel=True))
    if args.op == "sim":
        sols = simulate_benchmarks(get_benchmarks())
        print(sols)
