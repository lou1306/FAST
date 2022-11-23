'''
This file is part of an ICSE'18 submission that is currently under review. 
For more information visit: https://github.com/icse18-FAST/FAST.
    
This is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as 
published by the Free Software Foundation, either version 3 of the 
License, or (at your option) any later version.

This software is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this source.  If not, see <http://www.gnu.org/licenses/>.
'''

import os
import random
import re
import subprocess
import sys
import time
from collections import OrderedDict, defaultdict
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
from struct import pack, unpack
from subprocess import DEVNULL, PIPE
from tempfile import NamedTemporaryFile

from dotenv import load_dotenv

import lsh

load_dotenv()
# TODO eager check for required environment variables

def process_clause(line):
    if not line:
        return None
    elif line[0] not in ("c", "p"):
        return tuple(
            int(lit) for lit in line[:-1].split()
            if lit != "0")


def process_funccalls(line):
    return line \
    if line[0] == "c" and "return_value" in line \
    else None


def loadTestSuite(input_file, bbox=False, k=5):
    """INPUT
    (str)input_file: path of input file

    OUTPUT
    (dict)TS: key=tc_ID, val=set(covered lines)
    """
    TS = defaultdict()
    with open(input_file) as fin:
        tcID = 1
        for tc in fin:
            if bbox:
                TS[tcID] = tc[:-1]
            else:
                TS[tcID] = set(tc[:-1].split())
            tcID += 1
    shuffled = list(TS.items())
    random.shuffle(shuffled)
    TS = OrderedDict(shuffled)
    if bbox:
        TS = lsh.kShingles(TS, k)
    return TS


def loadSatTestSuite(input_file, bbox=False, k=5):
    """INPUT
    (str)input_file: path of input file

    OUTPUT
    (dict)TS: key=tc_ID, val=set(covered lines)
    """
    TS = defaultdict()
    with open(input_file) as fin:
        for tcID, tc in enumerate(fin, 1):
            if bbox:
                TS[tcID] = tc[:-1]
            else:
                TS[tcID] = set(tc[:-1].split())
    shuffled = list(TS.items())
    # random.shuffle(shuffled)
    TS = OrderedDict(shuffled)
    if bbox:
        TS = lsh.kShingles(TS, k)
    return TS


PACKAGE = re.compile(r"package ([A-Za-z0-9_.]+)")
CLASS = re.compile(r"public( final)? class ([A-Za-z0-9_]+)")
BOUND_WITH_UAS = 2

@lru_cache(maxsize=8)
def has_loops(entry_point):
    cmd = [
        "jbmc",
        "-cp", os.environ["FAST_JBMC_CP"],
        "--show-loops",
        entry_point
    ]
    x = subprocess.run(cmd, encoding="utf8", cwd=os.environ["FAST_JBMC_DIR"], stdout=PIPE)
    if x.returncode != 0:
        print(x.returncode)
        raise ValueError("Something bad happened while generating CNF")
    return "file" in x.stdout and "line" in x.stdout


def get_cnf(entry_point, dest_filename, unwind, *args):
    timeout_value = 500
    limit = 100
    cmd = [
        "jbmc",
        "-cp", os.environ["FAST_JBMC_CP"],
        "--unwind", str(unwind),
        "--dimacs",
        "--outfile", dest_filename,
        "--java-assume-inputs-integral",
        # "--java-assume-inputs-non-null",
        "--disable-uncaught-exception-check",
        # "--reachability-slice",
        # "--string-printable",
        # "--string-non-empty",
        "--drop-unused-functions",
        "--max-nondet-string-length", "0",
        "--max-nondet-array-length", "0",
        "--max-nondet-tree-depth", "1",
        # "--symex-driven-lazy-loading",
        # "--drop-unused-functions",
        # "--slice-formula",
        entry_point, *args]
    try:
        x = subprocess.run(
            cmd,
            cwd=os.environ["FAST_JBMC_DIR"],
            timeout=timeout_value, stderr=DEVNULL, stdout=DEVNULL)
        size = subprocess.check_output(["head", "-n", "1", dest_filename], encoding="utf8")
        if x.returncode == -6:
            # Invariant violation (happens sometimes)
            # TODO get invoked functions with javalang
            return "p cnf 99999999 99999999"
        elif x.returncode != 0:
            print(x.returncode)
            raise ValueError("Something bad happened while generating CNF")
    except subprocess.TimeoutExpired:
        return "p cnf 99999999 99999999"
        # Give up
        # size = "p cnf 0 0"
        # if "--slice-formula" not in args:
        #     # Restart with slicing
        #     return get_cnf(
        #         entry_point, dest_filename, 1, 
        #         *[*args, "--slice-formula"]
        #     )
        # else:

    if "cnf 0 0" in size:
        if not has_loops(entry_point):
            print(f"No assertions found and no loops, giving up.")
            return size
        elif unwind < limit:
            print(f"No assertions found for {unwind}, trying {unwind+1}...")
            return get_cnf(entry_point, dest_filename, unwind+1, *args)
        else:
            if "--unwinding-assertions" not in args:
                args = [*args, "--unwinding-assertions"]
                print(
                    f"No assertions found for {unwind}, "
                    f"restart at {BOUND_WITH_UAS} with unwinding assertions.")
                return get_cnf(entry_point, dest_filename, BOUND_WITH_UAS, *args)  # noqa: E501
            else:
                print(f"No assertions found for {unwind}, giving up.")
    return size


def storeSignatures(input_file, sigfile, hashes, bbox=False, k=5):
    with (
        open(sigfile, "w") as sigfile,
        open(input_file) as fin,
        NamedTemporaryFile(delete=False, suffix=".cnf") as cnf,
        NamedTemporaryFile(delete=False, suffix=".cnf") as reduced_cnf,
        ProcessPoolExecutor() as EXEC
    ):
        tcID = 1
        cnf.close()
        reduced_cnf.close()
        for tc in fin:
            if bbox:
                # shingling
                t = time.time()
                tc_ = tc[:-1]   
                pkg = PACKAGE.findall(tc_)[0]
                cls = CLASS.findall(tc_)[0][1]
                try:
                    print(pkg, cls, "..", sep=".")
                    size_original = get_cnf(f"{pkg}.{cls}.__TC", cnf.name, 1)
                    # TODO if for whatever reason the CNF cannot be generated, 
                    # we should prioritize the test. Sad, but sound
                except ValueError as err:
                    EXEC.shutdown()
                    raise err
                
                def minisat_pre(elim=True):
                    cmd = [
                            "minisat",
                            cnf.name,
                            "-no-solve",
                            f"-dimacs={reduced_cnf.name}"]
                    if not elim:
                        cmd.append("-no-elim")
                    try:
                        subprocess.check_output(cmd)
                    except subprocess.CalledProcessError as err:
                        # 10 (r. 20) just means minisat proved the cnf to be 
                        # SAT (r. UNSAT) while preprocessing. Nothing bad
                        if err.returncode not in (10, 20):
                            EXEC.shutdown
                            raise err

                end_char = "" if size_original[-1] == '\n' else '\n'
                print("Original CNF:          ", size_original, end=end_char)
                minisat_pre()
                # size_original = subprocess.check_output(["head", "-n", "1", cnf.name], encoding="utf8")
                size_reduced = subprocess.check_output(["head", "-n", "1", reduced_cnf.name], encoding="utf8")
                print("Reduced CNF:           ", size_reduced, end="")
                if "cnf 0 0" in size_reduced:
                    minisat_pre(elim=False)
                    size_reduced = subprocess.check_output(["head", "-n", "1", reduced_cnf.name], encoding="utf8")
                    print("Reduced CNF (no-elim): ", size_reduced, end="")


                with open(cnf.name) as f_cnf, open(reduced_cnf.name) as f_r:
                    tc_shingles = EXEC.map(process_clause, f_r, chunksize=10000)
                    calls = EXEC.map(process_funccalls, f_cnf, chunksize=10000)

                    tc_shingles = set(tc_shingles).union(calls)

                    # Original ICSE'18 code. In memoriam
                    # tc_shingles = set(c for c in clauses if c)
                    # print(tc_shingles)
                    # tc_shingles = set(
                    #     tuple(
                    #         int(lit) for lit in clause[:-1].split()
                    #         if lit != "0"
                    #     )
                    #     for clause in cnf
                    #     if clause and clause[0] not in ("c", "p")
                    # )

                sig = lsh.tcMinhashing((tcID, set(tc_shingles)), hashes)
                print(time.time() - t, "seconds")
                # print(sig)
                # input()
            else:
                tc_ = tc[:-1].split()
                sig = lsh.tcMinhashing((tcID, set(tc_)), hashes)
                
            for hash_ in sig:
                sigfile.write(repr(unpack('>d', hash_)[0]))
                sigfile.write(" ")
            sigfile.write("\n")
            tcID += 1

        os.remove(cnf.name)
        os.remove(reduced_cnf.name)


def loadSignatures(input_file):
    """INPUT
    (str)input_file: path of input file

    OUTPUT
    (dict)TS: key=tc_ID, val=set(covered lines), sigtime"""
    sig = {}
    start = time.time()
    with open(input_file, "r") as fin:
        tcID = 1
        for tc in fin:
            sig[tcID] = [pack('>d', float(i)) for i in tc[:-1].split()]
            tcID += 1
    return sig, time.time() - start


# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


# lsh + pairwise comparison with candidate set
def fast_pw(input_file, r, b, bbox=False, k=5, memory=False):
    """INPUT
    (str)input_file: path of input file
    (int)r: number of rows
    (int)b: number of bands
    (bool)bbox: True if BB prioritization
    (int)k: k-shingle size (for BB prioritization)
    (bool)memory: if True keep signature in memory and do not store them to file

    OUTPUT
    (list)P: prioritized test suite
    """
    n = r * b  # number of hash functions

    print(input_file, r, b, bbox, k, memory)

    hashes = [lsh.hashFamily(i) for i in range(n)]

    if memory:
        test_suite = loadTestSuite(input_file, bbox=bbox, k=k)
        # generate minhashes signatures
        mh_t = time.time()
        tcs_minhashes = {tc[0]: lsh.tcMinhashing(tc, hashes)
                         for tc in list(test_suite.items())}
        mh_time = time.time() - mh_t
        ptime_start = time.time()

    else:
        # loading input file and generating minhashes signatures
        sigfile = input_file.replace(".txt", ".sig")
        sigtimefile = "{}_sigtime.txt".format(input_file.split(".")[0])
        if not os.path.exists(sigfile):
            mh_t = time.time()
            storeSignatures(input_file, sigfile, hashes, bbox, k)
            mh_time = time.time() - mh_t
            with open(sigtimefile, "w") as fout:
                fout.write(repr(mh_time))
        else:
            with open(sigtimefile, "r") as fin:
                mh_time = eval(fin.read().replace("\n", ""))

        ptime_start = time.time()
        tcs_minhashes, load_time = loadSignatures(sigfile)

    tcs = set(tcs_minhashes.keys())

    BASE = 0.5
    SIZE = int(len(tcs)*BASE) + 1

    bucket = lsh.LSHBucket(list(tcs_minhashes.items()), b, r, n)

    prioritized_tcs = [0]

    # First TC
    selected_tcs_minhash = lsh.tcMinhashing((0, set()), hashes)
    first_tc = random.choice(list(tcs_minhashes.keys()))
    for i in range(n):
        if tcs_minhashes[first_tc][i] < selected_tcs_minhash[i]:
            selected_tcs_minhash[i] = tcs_minhashes[first_tc][i]
    prioritized_tcs.append(first_tc)
    tcs -= set([first_tc])
    del tcs_minhashes[first_tc]

    iteration, total = 0, float(len(tcs_minhashes))
    while len(tcs_minhashes) > 0:
        iteration += 1
        if iteration % 100 == 0:
            sys.stdout.write("  Progress: {}%\r".format(
                round(100*iteration/total, 2)))
            sys.stdout.flush()

        if len(tcs_minhashes) < SIZE:
            bucket = lsh.LSHBucket(list(tcs_minhashes.items()), b, r, n)
            SIZE = int(SIZE*BASE) + 1

        sim_cand = lsh.LSHCandidates(bucket, (0, selected_tcs_minhash),
                                     b, r, n)
        filtered_sim_cand = sim_cand.difference(prioritized_tcs)
        candidates = tcs - filtered_sim_cand

        if len(candidates) == 0:
            selected_tcs_minhash = lsh.tcMinhashing((0, set()), hashes)
            sim_cand = lsh.LSHCandidates(bucket, (0, selected_tcs_minhash),
                                         b, r, n)
            filtered_sim_cand = sim_cand.difference(prioritized_tcs)
            candidates = tcs - filtered_sim_cand
            if len(candidates) == 0:
                candidates = list(tcs_minhashes.keys())

        selected_tc, max_dist = random.choice(tuple(candidates)), -1
        for candidate in tcs_minhashes:
            if candidate in candidates:
                dist = lsh.jDistanceEstimate(
                    selected_tcs_minhash, tcs_minhashes[candidate])
                if dist > max_dist:
                    selected_tc, max_dist = candidate, dist

        for i in range(n):
            if tcs_minhashes[selected_tc][i] < selected_tcs_minhash[i]:
                selected_tcs_minhash[i] = tcs_minhashes[selected_tc][i]

        prioritized_tcs.append(selected_tc)
        tcs -= set([selected_tc])
        del tcs_minhashes[selected_tc]

    ptime = time.time() - ptime_start

    return mh_time, ptime, prioritized_tcs[1:]


# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #


def fast_(input_file, selsize, r, b, bbox=False, k=5, memory=False):
    """INPUT
    (str)input_file: path of input file
    (fun)selsize: size of candidate set
    (int)r: number of rows
    (int)b: number of bands
    (bool)bbox: True if BB prioritization
    (int)k: k-shingle size (for BB prioritization)
    (bool)memory: if True keep signature in memory and do not store them to file

    OUTPUT
    (list)P: prioritized test suite
    """
    n = r * b  # number of hash functions

    hashes = [lsh.hashFamily(i) for i in range(n)]

    if memory:
        test_suite = loadTestSuite(input_file, bbox=bbox, k=k)
        # generate minhashes signatures
        mh_t = time.time()
        tcs_minhashes = {tc[0]: lsh.tcMinhashing(tc, hashes)
                         for tc in list(test_suite.items())}
        mh_time = time.time() - mh_t
        ptime_start = time.time()

    else:
        # loading input file and generating minhashes signatures
        sigfile = input_file.replace(".txt", ".sig")
        sigtimefile = "{}_sigtime.txt".format(input_file.split(".")[0])
        if not os.path.exists(sigfile):
            mh_t = time.time()
            storeSignatures(input_file, sigfile, hashes, bbox, k)
            mh_time = time.time() - mh_t
            with open(sigtimefile, "w") as fout:
                fout.write(repr(mh_time))
        else:
            with open(sigtimefile, "r") as fin:
                mh_time = eval(fin.read().replace("\n", ""))

        ptime_start = time.time()
        tcs_minhashes, load_time = loadSignatures(sigfile)

    tcs = set(tcs_minhashes.keys())

    BASE = 0.5
    SIZE = int(len(tcs)*BASE) + 1

    bucket = lsh.LSHBucket(list(tcs_minhashes.items()), b, r, n)

    prioritized_tcs = [0]

    # First TC
    selected_tcs_minhash = lsh.tcMinhashing((0, set()), hashes)
    first_tc = random.choice(list(tcs_minhashes.keys()))
    for i in range(n):
        if tcs_minhashes[first_tc][i] < selected_tcs_minhash[i]:
            selected_tcs_minhash[i] = tcs_minhashes[first_tc][i]
    prioritized_tcs.append(first_tc)
    tcs -= set([first_tc])
    del tcs_minhashes[first_tc]

    iteration, total = 0, float(len(tcs_minhashes))
    while len(tcs_minhashes) > 0:
        iteration += 1
        if iteration % 100 == 0:
            sys.stdout.write("  Progress: {}%\r".format(
                round(100*iteration/total, 2)))
            sys.stdout.flush()

        if len(tcs_minhashes) < SIZE:
            bucket = lsh.LSHBucket(list(tcs_minhashes.items()), b, r, n)
            SIZE = int(SIZE*BASE) + 1

        sim_cand = lsh.LSHCandidates(bucket, (0, selected_tcs_minhash),
                                     b, r, n)
        filtered_sim_cand = sim_cand.difference(prioritized_tcs)
        candidates = tcs - filtered_sim_cand

        if len(candidates) == 0:
            selected_tcs_minhash = lsh.tcMinhashing((0, set()), hashes)
            sim_cand = lsh.LSHCandidates(bucket, (0, selected_tcs_minhash),
                                         b, r, n)
            filtered_sim_cand = sim_cand.difference(prioritized_tcs)
            candidates = tcs - filtered_sim_cand
            if len(candidates) == 0:
                candidates = list(tcs_minhashes.keys())

        to_sel = min(selsize(len(candidates)), len(candidates))
        selected_tc_set = random.sample(tuple(candidates), to_sel)

        for selected_tc in selected_tc_set:
            for i in range(n):
                if tcs_minhashes[selected_tc][i] < selected_tcs_minhash[i]:
                    selected_tcs_minhash[i] = tcs_minhashes[selected_tc][i]

            prioritized_tcs.append(selected_tc)
            tcs -= set([selected_tc])
            del tcs_minhashes[selected_tc]

    ptime = time.time() - ptime_start

    return mh_time, ptime, prioritized_tcs[1:]
