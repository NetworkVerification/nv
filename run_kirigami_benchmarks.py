#!/usr/bin/env python3

# Main module to generate, run and tabulate the Kirigami benchmarks.
import argparse
import sys
import os
import re
from datetime import datetime
from gen_part_nv import gen_part_nv, HORIZONTAL, VERTICAL
from tabulate_sp_bench import run_benchmark, write_csv, DISTINCT_OPERATIONS

BENCH_DIR = "benchmarks/SinglePrefix"

def get_benchmarks():
    """Return the list of input benchmark files with their destinations."""
    benches = [
        (f"{BENCH_DIR}/FAT4/sp4.nv", 10),
        (f"{BENCH_DIR}/FAT8/sp8.nv", 12),
        (f"{BENCH_DIR}/FAT10/sp10.nv", 13),
        (f"{BENCH_DIR}/FAT12/sp12.nv", 64),
        (f"{BENCH_DIR}/FAT16/sp16.nv", 0),
        (f"{BENCH_DIR}/FAT20/sp20.nv", 0),
    ]
    return benches


def create_benchmarks(gen_horizontal, gen_vertical):
    """
    Generate the necessary benchmarks to use.
    """
    for (inputf, dest) in get_benchmarks():
        if gen_horizontal:
            gen_part_nv(inputf, dest, HORIZONTAL)
        if gen_vertical:
            gen_part_nv(inputf, dest, VERTICAL)


def clean_benchmarks(dry_run):
    pat = re.compile("^sp\d*-(v?)part\d*\.nv$", re.M)
    for root, dirs, files in os.walk(BENCH_DIR):
        for fname in files:
            if pat.search(fname):
                bench_path = os.path.join(root, fname)
                if dry_run:
                    print(f"Removing {bench_path}")
                else:
                    os.remove(bench_path)


def tabulate_fattree_benchmarks(sizes=[4, 8, 10, 12, 16, 20], timeout=3600,trials=10):
    """
    Run all the vertical and horizontal benchmarks.
    """
    runs = []
    for size in sizes:
        directory = f"{BENCH_DIR}/FAT{size}"
        results = run_benchmark(directory, "sp{}{}.nv", size, timeout, trials, DISTINCT_OPERATIONS)
        runs.append(results)
    return runs


def save_results(runs):
    timestamp = datetime.now()
    time = timestamp.strftime("%Y-%m-%d-%H:%M:%S")
    return write_csv(runs, f"kirigami-results-{time}.csv")


if __name__ == "__main__":
    OP = sys.argv[1]
    if OP == "make":
        create_benchmarks(True, True)
    if OP == "clean":
        clean_benchmarks(dry_run=False)
    if OP == "list":
        clean_benchmarks(dry_run=True)
    if OP == "run":
        save_results(tabulate_fattree_benchmarks(sizes=[4,8]))
