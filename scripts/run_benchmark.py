#!/usr/bin/env python3
import argparse
from enum import Enum
import multiprocessing
import subprocess
import os
from typing import Optional


class RunSmtResult(Enum):
    SUCCEEDED = 0
    TIMEOUT = 1
    ERROR = 2


def run_nv_smt(
    path: str, cut: Optional[str], z3time: int, time: float, cores: int
) -> tuple[RunSmtResult, str]:
    """
    Run nv's SMT tool and return the result and its output.
    If it doesn't finish within the given time, kill it.
    """
    nvcmd = "nv.opt"
    nvpath = os.path.join(os.getcwd(), nvcmd)
    if not os.path.exists(nvpath):
        raise Exception(
            f"Did not find '{nvcmd}' executable in the current working directory!"
        )
    # set verbose, SMT flags, and partitioning if needed
    args = [nvpath, "-v", "-m", "-t", str(z3time)]
    if cut is not None:
        # run on multiple cores
        if cores > 1:
            args += ["-p", str(cores)]
        args += ["-k", path]
    else:
        args += [path]
    output = f"Running {' '.join(args)}\n"
    try:
        proc = subprocess.run(
            args,
            text=True,
            check=True,
            capture_output=True,
            timeout=time,
            encoding="utf-8",
        )
        return RunSmtResult.SUCCEEDED, output + proc.stdout
    except subprocess.CalledProcessError as exn:
        return RunSmtResult.ERROR, "Error: {exn}"
    except subprocess.TimeoutExpired as exn:
        partial_output = exn.output.decode("utf-8")
        return (
            RunSmtResult.TIMEOUT,
            partial_output + f"Timed out (external) at {exn.timeout}",
        )


def run_benchmarks(
    benchdir, benches: list[tuple], z3time, time, cores
) -> dict[str, str]:
    """
    Run the given benchmarks in the given directory in sequence (once each).
    Return a log of output and a dictionary with the benchmark results for each cut.
    """

    benchmark_outputs = {}
    for (cut, benchmark) in benches:
        result, output = run_nv_smt(
            os.path.join(benchdir, benchmark), cut, z3time, time, cores
        )
        if cut is None:
            cut = "monolithic"
        benchmark_outputs[cut] = output
    return benchmark_outputs


def run_trials_sync(
    benchdir,
    benches: list[tuple],
    z3time: float,
    time: float,
    trials: int,
    cores: int,
) -> dict[int, dict[str, str]]:
    """
    Run trials of the given benchmarks and return a dictionary of profiling information.
    """
    return {
        i: run_benchmarks(benchdir, benches, z3time, time, cores) for i in range(trials)
    }


def run_trials_parallel(
    benchdir,
    benches,
    z3time: float,
    time: float,
    trials: int,
    cores: int,
) -> dict[int, dict[str, str]]:
    """
    Run the benchmarks in the given directory and return a dictionary of
    profiling information.
    Runs each trial in parallel.
    """
    with multiprocessing.Pool(processes=trials) as pool:
        args = [(benchdir, benches, z3time, time, cores) for _ in range(trials)]
        runs = pool.starmap(run_benchmarks, args)
        return dict(enumerate(runs))


def run_benchmark_txt(
    txtpath: str, z3time: float, timeout: float, trials: int, cores: int
) -> dict[str, dict[int, dict[str, str]]]:
    """
    Run a benchmark.txt file.
    Each line of the file has the following format:
    [directory] [monolithic benchmark] [cut name:cut benchmarks]*
    Filenames must not have spaces!
    Files can contain line comments beginning with a '#'.
    Return a dict from benchmarks to dicts from trials to dicts from cuts to outputs
    (triply-nested dict).
    """
    runs = {}
    with open(txtpath, "r") as benchmark_file:
        for benchmarks in benchmark_file.readlines():
            # skip comments
            if benchmarks.startswith("#"):
                continue
            directory, monolithic, *cuts = benchmarks.split()
            benches: list[tuple[Optional[str], str]] = [(None, monolithic)]
            for cut in cuts:
                cut_name, cut_path = cut.split(":")
                benches.append((cut_name, cut_path))
            try:
                results = run_trials_parallel(
                    directory,
                    benches,
                    z3time=z3time,
                    time=timeout,
                    trials=trials,
                    cores=cores,
                )
                benchmark_key = os.path.join(directory, monolithic)
                runs[benchmark_key] = results
            except KeyboardInterrupt:
                print("User interrupted benchmarking. Exiting with partial results...")
                break
    return runs


def parser():
    parser = argparse.ArgumentParser(
        description="Frontend for running Kirigami benchmarks."
    )
    parser.add_argument(
        "file",
        help="benchmark.txt file describing which benchmarks to run",
    )
    parser.add_argument(
        "-n",
        "--trials",
        type=int,
        help="number of trials to run (default: %(default)s)",
        default=5,
    )
    parser.add_argument(
        "-z",
        "--z3time",
        type=int,
        help="number of seconds to run each trial for in z3 (default: %(default)s)",
        default=3600,
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        help="number of seconds to run each trial for (default: %(default)s)",
        default=3600,
    )
    parser.add_argument(
        "-p",
        "--parallel",
        type=int,
        help="number of cores to use for each trial (default: %(default)s)",
        default=1,
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="print the trial's stdout",
    )
    return parser


if __name__ == "__main__":
    args = parser().parse_args()
    runs = run_benchmark_txt(
        args.file, args.z3time, args.timeout, args.trials, args.parallel
    )
    if args.verbose:
        for (b, trials) in runs.items():
            for (t, cuts) in trials.items():
                for (c, output) in cuts.items():
                    print(f"Benchmark {b}, trial {t}, cut {c}:")
                    print(output)
