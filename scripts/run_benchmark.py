#!/usr/bin/env python3
"""
Commandline helper to run nv's SMT tool on various benchmarks.
Accepts a benchmark.txt file which can specify benchmarks to run,
where each line of the file has the format:
    [directory] [monolithic benchmark] [cut name:cut benchmarks]*
(first listed file is the monolithic benchmark)
Filenames and cut names must not have spaces or colons!
Files can contain line comments beginning with a '#'.
Each benchmark's result is then saved to a benchmark_output.txt file.
"""
import argparse
from dataclasses import dataclass
from enum import Enum
import multiprocessing
import subprocess
import os
from typing import Optional

# the result of running nv -smt
class RunSmtResult(Enum):
    SUCCEEDED = 0
    TIMEOUT = 1
    ERROR = 2

    def __str__(self):
        match self:
            case RunSmtResult.SUCCEEDED:
                return "Success"
            case RunSmtResult.TIMEOUT:
                return "Timeout"
            case RunSmtResult.ERROR:
                return "Error"


@dataclass
class BenchmarkParams:
    """The set of parameters one can specify for running the benchmarks."""

    # the default name of the NV executable
    # we use nv.opt, which is the version with optimizations
    nv_exe_path: str = "nv.opt"
    # the maximum time for z3 to run, as specified to nv via the -t flag
    z3_timeout: int = 3600
    # the maximum time for nv to run, as specified to subprocess.run
    nv_timeout: float = 3600
    # the number of cores nv may use to parallelize fragment solving
    nv_cores: int = 1
    # the number of trials to run
    ntrials: int = 1
    # the name of the directory in which logs should be saved
    results_directory_name: str = "results"
    # whether or not trials should run as separate processes
    parallelize_trials: bool = False
    # whether or not to announce a trial before it runs
    announce_trials: bool = False


def run_nv_smt(
    benchmark_path: str,
    cut: bool,
    params: BenchmarkParams,
) -> tuple[RunSmtResult, str]:
    """
    Run nv's SMT tool and return the result and its output.
    The nv executable is specified by nv_exe_path, and the benchmark to run
    is specified by benchmark_path.
    If it doesn't finish within the given time, kill it.
    """
    # set verbose, SMT flags, and partitioning if needed
    args = [params.nv_exe_path, "-v", "-m", "-t", str(params.z3_timeout)]
    if cut:
        # run on multiple cores
        if params.nv_cores > 1:
            args += ["-p", str(params.nv_cores)]
        args += ["-k", benchmark_path]
    else:
        args += [benchmark_path]
    trial_args = f"Running {' '.join(args)}"
    if params.announce_trials:
        print(trial_args)
    try:
        proc = subprocess.run(
            args,
            text=True,
            check=True,
            capture_output=True,
            timeout=params.nv_timeout,
            encoding="utf-8",
        )
        return RunSmtResult.SUCCEEDED, "\n".join([trial_args, proc.stdout])
    except subprocess.CalledProcessError as exn:
        return RunSmtResult.ERROR, "Error: {exn}"
    except subprocess.TimeoutExpired as exn:
        partial_output = exn.output.decode("utf-8")
        return (
            RunSmtResult.TIMEOUT,
            partial_output + f"Timed out (external) at {exn.timeout}",
        )


def log_nv_smt_run(
    benchmark_path: str,
    cut: bool,
    params: BenchmarkParams,
    log_file: str,
):
    """Run the given nv executable for the given benchmark, and log the results."""
    result, output = run_nv_smt(benchmark_path, cut, params)
    with open(log_file, "w") as log:
        log.write(f"RESULT: {result}\n")
        log.write(output)


def run_benchmarks(
    benchdir,
    benches: list[tuple[str | None, str]],
    params: BenchmarkParams,
    results_dir: str,
):
    """
    Run the given benchmarks in the given directory in parallel, spawning a separate process for each benchmark.
    Log each benchmark's result to a file in results_dir.
    """
    benchmark_args = [
        (
            os.path.join(benchdir, benchmark),
            cut is not None,
            params,
            os.path.join(
                results_dir, f"{benchmark}-{cut if cut else 'mono'}{trial_idx}.txt"
            ),
        )
        for (cut, benchmark) in benches
        for trial_idx in range(params.ntrials)
    ]
    if params.parallelize_trials:
        with multiprocessing.Pool(processes=params.ntrials * len(benches)) as pool:
            pool.starmap(log_nv_smt_run, benchmark_args)
    else:
        for args in benchmark_args:
            log_nv_smt_run(*args)


def run_benchmark_txt(
    txtpath: str,
    params: BenchmarkParams,
) -> None:
    """
    Run a benchmark.txt file.
    Each line of the file has the following format:
    [directory] [monolithic benchmark] [cut name:cut benchmarks]*
    Filenames and cut names must not have spaces!
    Files can contain line comments beginning with a '#'.
    Return a dict from benchmarks to dicts from trials to dicts from cuts to outputs
    (triply-nested dict).
    """
    if not os.path.exists(params.nv_exe_path):
        raise Exception(f"Did not find '{params.nv_exe_path}' executable!")
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
                results_dir = os.path.join(directory, params.results_directory_name)
                # create the results directory if it is missing
                if not os.path.exists(results_dir):
                    os.mkdir(results_dir)
                run_benchmarks(
                    directory,
                    benches,
                    params,
                    results_dir=results_dir,
                )
            except KeyboardInterrupt:
                print("User interrupted benchmarking. Exiting with partial results...")
                break


def parser():
    default_params = BenchmarkParams()
    parser = argparse.ArgumentParser(
        description="Frontend for running Kirigami benchmarks."
    )
    parser.add_argument(
        "file",
        help="benchmark.txt file describing which benchmarks to run",
    )
    parser.add_argument(
        "-x",
        "--nv-path",
        default=os.path.join(os.getcwd(), default_params.nv_exe_path),
        help="which executable to run as NV (default: %(default))",
    )
    parser.add_argument(
        "-d",
        "--results-dir",
        default=default_params.results_directory_name,
        help="name of the directory to store results (default: %(default)) inside the benchmarks' directory",
    )
    parser.add_argument(
        "-n",
        "--trials",
        type=int,
        help="number of trials to run (default: %(default)s)",
        default=default_params.ntrials,
    )
    parser.add_argument(
        "-z",
        "--z3time",
        type=int,
        help="number of seconds to run each trial for in z3 (default: %(default)s)",
        default=default_params.z3_timeout,
    )
    parser.add_argument(
        "-t",
        "--timeout",
        type=int,
        help="number of seconds to run each trial for (default: %(default)s)",
        default=default_params.nv_timeout,
    )
    parser.add_argument(
        "-p",
        "--parallel",
        type=int,
        help="number of cores to use for each trial (default: %(default)s)",
        default=default_params.nv_cores,
    )
    parser.add_argument(
        "-P",
        "--parallel-trials",
        action="store_true",
        help="if specified, run each benchmark in a directory as a separate process",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        action="store_true",
        help="print when trials are run",
    )
    return parser


if __name__ == "__main__":
    args = parser().parse_args()
    params = BenchmarkParams(
        nv_exe_path=args.nv_path,
        results_directory_name=args.results_dir,
        z3_timeout=args.z3time,
        nv_timeout=args.timeout,
        nv_cores=args.parallel,
        ntrials=args.trials,
        parallelize_trials=args.parallel_trials,
        announce_trials=args.verbose,
    )
    run_benchmark_txt(args.file, params)
