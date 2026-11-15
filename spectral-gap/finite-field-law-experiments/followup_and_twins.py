#!/usr/bin/env python3
"""Exploratory larger-N follow-up and exact adjacent-twin diagnostics.

Chosen after observing the first study's lambda2 discrepancy. Original
samples are replayed for twin counts ONLY, without recomputing ranks.
"""
from pathlib import Path
import csv
import importlib.util
import json
import math
import sys
import time

import numpy as np

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("initial_corank_study", HERE/"k4_corank_experiment.py")
exp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exp)
FOLLOW = HERE/"followup"
FOLLOW.mkdir(exist_ok=True)
SEED = 2026111501409
SIZES = [60, 61, 99, 100]
PLANNED = [400, 400, 300, 300]


def twins(a):
    closed = a.astype(np.uint8, copy=True)
    closed[np.diag_indices(len(a))] = 1
    packed = np.packbits(closed, axis=1)
    _, counts = np.unique(packed, axis=0, return_counts=True)
    return int(np.sum(counts*(counts-1)//2)), int(np.sum(counts-1))


def main_twin_replay():
    original = json.loads((HERE/"results.json").read_text())
    raw = {N: [] for N in exp.SIZES}
    with (HERE/"samples.csv").open() as handle:
        for row in csv.DictReader(handle):
            raw[int(row["N"])].append(row)
    streams = np.random.SeedSequence(exp.SEED).spawn(len(exp.SIZES))
    diagnostics = []
    with (HERE/"main-twin-diagnostics.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["N", "sample", "excess_lambda2", "adjacent_twin_pairs", "duplicate_row_deficiency"])
        for N, stream in zip(exp.SIZES, streams):
            rng = np.random.default_rng(stream)
            pairs, conditional, unconditional = [], [], []
            for j, row in enumerate(raw[N]):
                a = exp.sample_k4_lift(N, rng)
                count, deficiency = twins(a)
                excess = int(row["excess_lambda2"])
                assert count == 0 or excess >= 1
                pairs.append(count)
                unconditional.append(excess)
                if count == 0:
                    conditional.append(excess)
                writer.writerow([N, j+1, excess, count, deficiency])
            pairs = np.asarray(pairs)
            diagnostics.append({"N": N, "samples": len(pairs),
                                "mean_twin_edges": float(np.mean(pairs)),
                                "mean_twin_edges_SE": float(np.std(pairs, ddof=1)/math.sqrt(len(pairs))),
                                "exact_expected_twin_edges": 6/N,
                                "graphs_with_twins": int(np.sum(pairs > 0)),
                                "fraction_with_twins": float(np.mean(pairs > 0)),
                                "lambda2_excess0_unconditional": unconditional.count(0)/len(unconditional),
                                "lambda2_excess0_given_no_twins": conditional.count(0)/len(conditional),
                                "no_twin_graphs": len(conditional),
                                "no_twin_excess_histogram": {str(k): conditional.count(k) for k in range(max(conditional)+1)},
                                "every_twin_graph_has_positive_lambda2_excess": True})
    (HERE/"main-twin-summary.json").write_text(json.dumps(diagnostics, indent=2)+"\n")
    return diagnostics


def main():
    begin = time.monotonic()
    twin_diagnostics = main_twin_replay()
    pilot = np.random.default_rng(SEED+1949)
    pilots = []
    for N in SIZES:
        tick = time.monotonic()
        for _ in range(4):
            exp.excess_pair(exp.sample_k4_lift(N, pilot))
        pilots.append({"N": N, "excluded_samples": 4,
                       "seconds_per_graph_two_ranks": (time.monotonic()-tick)/4})
    estimate = sum(x["seconds_per_graph_two_ranks"]*m for x, m in zip(pilots, PLANNED))
    scale = min(1., 170/max(estimate, .001))
    targets = [max(100, int(m*scale)//25*25) for m in PLANNED]
    streams = np.random.SeedSequence(SEED).spawn(len(SIZES))
    rngs = [np.random.default_rng(s) for s in streams]
    observed = {N: [] for N in SIZES}
    print(json.dumps({"stage": "followup", "pilot_estimated_seconds": estimate,
                      "fixed_targets": targets}), flush=True)
    sampling_start, last = time.monotonic(), time.monotonic()
    with (FOLLOW/"samples.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["N", "sample", "nullity_lambda0", "excess_lambda0", "nullity_lambda2", "excess_lambda2", "adjacent_twin_pairs"])
        while any(len(observed[N]) < m for N, m in zip(SIZES, targets)):
            for N, target, rng in zip(SIZES, targets, rngs):
                for _ in range(min(25, target-len(observed[N]))):
                    a = exp.sample_k4_lift(N, rng)
                    x0, x2 = exp.excess_pair(a)
                    pair_count, _ = twins(a)
                    assert pair_count == 0 or x2 >= 1
                    observed[N].append((x0, x2, pair_count))
                    writer.writerow([N, len(observed[N]), x0+1, x0, x2+3, x2, pair_count])
            if time.monotonic()-last > 12:
                print(json.dumps({"stage": "followup", "counts": {str(N): len(observed[N]) for N in SIZES},
                                  "seconds": time.monotonic()-sampling_start}), flush=True)
                last = time.monotonic()
                handle.flush()
    constant, probs = exp.reference_law(3)
    groups = []
    for N, m, child in zip(SIZES, targets, streams):
        v = np.asarray(observed[N], dtype=np.int64)
        no_twins = v[v[:, 2] == 0, 1]
        groups.append({"N": N, "samples": m, "seed_spawn_key": list(child.spawn_key),
                       "shifts": {"0": exp.summarize(v[:, 0], probs), "2": exp.summarize(v[:, 1], probs)},
                       "twins": {"mean_pairs": float(np.mean(v[:, 2])), "expected_pairs": 6/N,
                                 "graphs_with_twins": int(np.sum(v[:, 2] > 0)),
                                 "excess0_given_no_twins": float(np.mean(no_twins == 0))}})
    contrasts = []
    for ga, gb in [(groups[0], groups[1]), (groups[2], groups[3])]:
        for lam in ["0", "2"]:
            ba, bb = ga["shifts"][lam]["bins"][0], gb["shifts"][lam]["bins"][0]
            se = math.hypot(ba["binomial_SE"], bb["binomial_SE"])
            contrasts.append({"divisible_N": ga["N"], "neighbor_N": gb["N"],
                              "lambda": int(lam), "difference": ba["frequency"]-bb["frequency"],
                              "SE": se, "z": (ba["frequency"]-bb["frequency"])/se if se else 0.})
    results = {"study_type": "posthoc exploratory larger-size follow-up", "seed": SEED,
               "prime": 3, "actual_fixed_targets": targets, "planned_targets": PLANNED,
               "pilot": pilots, "pilot_excluded_from_histograms": True,
               "sampling_elapsed_seconds": time.monotonic()-sampling_start,
               "validation": json.loads((HERE/"results.json").read_text())["validation"],
               "reference": {"normalizing_constant": constant, "probabilities": probs},
               "groups": groups, "divisibility_contrasts": contrasts,
               "original_study_twin_diagnostics": twin_diagnostics,
               "total_followup_seconds": time.monotonic()-begin}
    (FOLLOW/"results.json").write_text(json.dumps(results, indent=2)+"\n")
    with (FOLLOW/"histograms.csv").open("w", newline="") as handle:
        fields = ["N", "lambda", "samples"]+list(groups[0]["shifts"]["0"]["bins"][0])
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for g in groups:
            for lam, info in g["shifts"].items():
                for b in info["bins"]:
                    writer.writerow({"N": g["N"], "lambda": lam, "samples": g["samples"], **b})
    exp.HERE = FOLLOW
    exp.SEED = SEED
    exp.make_figure(results, probs)
    exp.write_report(results)
    (FOLLOW/"REPORT.txt").write_text(
        "EXPLORATORY FOLLOW-UP: selected after the original finite-N discrepancy.\n\n"
        +(FOLLOW/"REPORT.txt").read_text())
    print(json.dumps({"stage": "complete", "counts": targets,
                      "seconds": results["sampling_elapsed_seconds"],
                      "summary": [{"N": g["N"], "shift": lam, "hist": s["histogram"],
                                   "TV": s["empirical_total_variation_from_reference"]}
                                  for g in groups for lam, s in g["shifts"].items()]}), flush=True)


if __name__ == "__main__":
    main()
