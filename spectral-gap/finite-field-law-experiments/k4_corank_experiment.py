#!/usr/bin/env python3
"""Independent exact-rank experiment, with no full-kernel-code imports.

Six uniform independent permutation matchings generate each K4 N-lift.
All elimination is integer arithmetic modulo3, using NumPy broadcasting.
Only this experiment directory receives output.
"""
from pathlib import Path
import csv
import hashlib
import itertools
import json
import math
import platform
import time

import numpy as np

HERE = Path(__file__).resolve().parent
P = 3
SIZES = [12, 13, 30, 31]
PLANNED_COUNTS = [3000, 3000, 600, 600]
SEED = 2026111500731
SHIFTS = {0: 1, 2: 3}


def rank_mod_numpy(matrix, p=3):
    """Forward row elimination. No floats, inverses, eigensolvers or SVD."""
    a = np.array(matrix, dtype=np.int64, copy=True) % p
    m, n = a.shape
    rank = 0
    for j in range(n):
        candidates = np.flatnonzero(a[rank:, j])
        if candidates.size == 0:
            continue
        pivot = rank+int(candidates[0])
        if pivot != rank:
            a[[rank, pivot], :] = a[[pivot, rank], :]
        inverse = pow(int(a[rank, j]), -1, p)
        if inverse != 1:
            a[rank, j:] = a[rank, j:]*inverse % p
        active = np.flatnonzero(a[rank+1:, j])+rank+1
        if active.size:
            factors = a[active, j].copy()
            a[active, j:] = (a[active, j:]
                              -factors[:, None]*a[rank, j:][None, :]) % p
        rank += 1
        if rank == m:
            break
    return rank


def brute_kernel_size(matrix, p):
    m, n = len(matrix), len(matrix[0])
    return sum(all(sum(matrix[i][j]*x[j] for j in range(n)) % p == 0
                   for i in range(m))
               for x in itertools.product(range(p), repeat=n))


def validate_new_rank_routine():
    rng = np.random.default_rng(994371)
    checked = 0
    for n in range(1, 6):
        for _ in range(5):
            a = rng.integers(0, P, size=(n, n), dtype=np.int64)
            r = rank_mod_numpy(a, P)
            assert brute_kernel_size(a.tolist(), P) == P**(n-r)
            checked += 1
    base = np.ones((4, 4), dtype=np.int64)-np.eye(4, dtype=np.int64)
    base_dimensions = {}
    for lam, expected in SHIFTS.items():
        a = base-lam*np.eye(4, dtype=np.int64)
        dim = 4-rank_mod_numpy(a, P)
        assert dim == expected and brute_kernel_size(a.tolist(), P) == P**dim
        base_dimensions[str(lam)] = dim
    return {"brute_force_small_rank_checks": checked,
            "base_kernel_dimensions_independently_checked": base_dimensions}


def sample_k4_lift(N, rng):
    n = 4*N
    a = np.zeros((n, n), dtype=np.int64)
    offset = np.arange(N)
    for i in range(4):
        for j in range(i+1, 4):
            perm = rng.permutation(N)
            rows, cols = i*N+offset, j*N+perm
            a[rows, cols] = 1
            a[cols, rows] = 1
    return a


def excess_pair(a):
    n = len(a)
    d0 = n-rank_mod_numpy(a, P)
    shifted = a.copy()
    shifted[np.diag_indices(n)] = -2
    d2 = n-rank_mod_numpy(shifted, P)
    assert d0 >= 1 and d2 >= 3, (n, d0, d2)
    return d0-1, d2-3


def reference_law(p):
    weights = [1.0]
    for k in range(1, 30):
        weights.append(weights[-1]/(p**k-1))
        if weights[-1] < 1e-40:
            break
    constant = 1/sum(weights)
    product = math.prod(1-p**(-(2*j-1)) for j in range(1, 101))
    assert abs(constant-product) < 2e-15
    probabilities = [constant*w for w in weights]
    assert abs(sum(probabilities)-1) < 1e-14
    return constant, probabilities


def wilson(count, m, z=1.959963984540054):
    phat = count/m
    den = 1+z*z/m
    center = (phat+z*z/(2*m))/den
    half = z*math.sqrt(phat*(1-phat)/m+z*z/(4*m*m))/den
    return max(0.0, center-half), min(1.0, center+half)


def summarize(values, probabilities):
    m = len(values)
    hist = {int(k): int(v) for k, v in zip(*np.unique(values, return_counts=True))}
    bins = []
    for k in range(max(5, max(hist)+1)+1):
        c = hist.get(k, 0)
        empirical = c/m
        expected = probabilities[k] if k < len(probabilities) else 0.0
        se = math.sqrt(empirical*(1-empirical)/m)
        nullse = math.sqrt(expected*(1-expected)/m)
        low, high = wilson(c, m)
        bins.append({"excess": k, "count": c, "frequency": empirical,
                     "binomial_SE": se, "wilson95_low": low, "wilson95_high": high,
                     "reference_probability": expected, "reference_expected_count": m*expected,
                     "reference_binomial_SE": nullse,
                     "reference_standardized_difference": (empirical-expected)/nullse if nullse else None})
    tv = sum(abs(hist.get(k, 0)/m-(probabilities[k] if k < len(probabilities) else 0))
             for k in range(max(max(hist)+1, len(probabilities))))/2
    powers = np.power(float(P), np.asarray(values, dtype=np.float64))
    return {"samples": m, "histogram": {str(k): hist.get(k, 0) for k in range(max(hist)+1)},
            "maximum_observed_excess": max(hist), "bins": bins,
            "empirical_total_variation_from_reference": tv,
            "mean_p_to_excess": float(np.mean(powers)),
            "mean_p_to_excess_SE": float(np.std(powers, ddof=1)/math.sqrt(m)),
            "reference_mean_p_to_excess": 2.0}


def make_figure(results, probabilities):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False,
                         "axes.spines.right": False, "savefig.dpi": 180})
    fig, axes = plt.subplots(2, 2, figsize=(10, 7.2), sharex=True, sharey=True)
    ref = list(probabilities[:4])+[sum(probabilities[4:])]
    colors = {"0": "#2875aa", "2": "#c66b23"}
    marks = {"0": "o", "2": "s"}
    for ax, group in zip(axes.flat, results["groups"]):
        ax.plot(range(5), ref, "k.-", lw=1.2, ms=5, label="reference law")
        for label, offset in [("0", -0.075), ("2", 0.075)]:
            info = group["shifts"][label]
            hist, m = info["histogram"], info["samples"]
            counts = [int(hist.get(str(k), 0)) for k in range(4)]
            counts.append(sum(int(v) for k, v in hist.items() if int(k) >= 4))
            for k, count in enumerate(counts):
                low, high = wilson(count, m)
                x = k+offset
                if count == 0:
                    ax.plot(x, high, "v", ms=5.5, color=colors[label], alpha=.8)
                else:
                    y = count/m
                    ax.errorbar(x, y, yerr=[[y-low], [high-y]], fmt=marks[label],
                                color=colors[label], ms=4.5, capsize=2, lw=1)
        residue = "3 divides N" if group["N"] % 3 == 0 else "3 does not divide N"
        ax.set_title(f"N = {group['N']}, {residue}; m = {group['samples']:,}")
        ax.set_yscale("log")
        ax.set_ylim(6e-6, 1.05)
        ax.set_xlim(-.35, 4.35)
        ax.set_xticks(range(5), ["0", "1", "2", "3", "≥4"])
        ax.grid(axis="y", alpha=.18)
    for ax in axes[1]:
        ax.set_xlabel("Excess modular corank")
    for ax in axes[:, 0]:
        ax.set_ylabel("Probability (log scale)")
    handles = [Line2D([0], [0], color="k", marker=".", label="Proposed symmetric limit"),
               Line2D([0], [0], color=colors["0"], marker="o", ls="none", label="λ = 0, old corank 1"),
               Line2D([0], [0], color=colors["2"], marker="s", ls="none", label="λ = 2, old corank 3"),
               Line2D([0], [0], color="gray", marker="v", ls="none", label="Zero counts: upper 95% bound")]
    fig.legend(handles=handles, loc="upper center", ncol=2, frameon=False, bbox_to_anchor=(.5, .975))
    fig.suptitle("Excess corank of exact random K₄ lifts over F₃", y=1.025, fontsize=14)
    fig.text(.5, .005, "Error bars: 95% Wilson intervals. Independent lift draws; both shifts use the same graph. Finite-size experiment.",
             ha="center", fontsize=8.5)
    fig.tight_layout(rect=(0, .035, 1, .89))
    fig.savefig(HERE/"observed-vs-symmetric-law.pdf", bbox_inches="tight")
    fig.savefig(HERE/"observed-vs-symmetric-law.png", bbox_inches="tight")
    plt.close(fig)


def write_report(results):
    out = ["EXACT K4-LIFT FINITE-FIELD CORANK EXPERIMENT", "15 November 2026", "",
           "New scientific validation only; no old kernel code or tests imported.",
           "The proposed limiting law is a reference, not inferred from this experiment.", "",
           f"Fixed study seed: {SEED}; NumPy PCG64/SeedSequence, one stream per N.",
           "Each graph uses six independent uniform permutation matchings.",
           "Elimination uses int64 row operations modulo3, with no floating rank or eigenvalues.",
           "Both shifts are computed on the SAME graph; graphs are independent across samples and N.",
           "The old base coranks are1 forlambda0 and3 forlambda2, checked by brute force.",
           f"Rank routine validation: {results['validation']['brute_force_small_rank_checks']} small new matrices checked by exhaustive kernel counts.", "",
           f"Reference C = {results['reference']['normalizing_constant']:.12g}.",
           "pi_k=C/product_{j=1}^k(3^j-1). Probabilities sum to1; normalization was independently checked by the odd Euler product.",
           "Reported SE is sqrt(phat*(1-phat)/m). Zero-count SE is zero, so Wilson95 intervals are also reported.",
           "Unadjusted z diagnostics are not familywise hypothesis tests and compare finite N with a limiting reference.", ""]
    for group in results["groups"]:
        out += [f"N={group['N']}; vertices={4*group['N']}; graphs={group['samples']}; Nmod3={group['N']%3}",
                "="*76]
        for label in ["0", "2"]:
            info = group["shifts"][label]
            out += [f"lambda={label}; old corank={SHIFTS[int(label)]}",
                    "k   count    observed       binomial_SE     Wilson95_low    Wilson95_high    reference       z_ref"]
            for b in info["bins"]:
                out.append(f"{b['excess']:<3} {b['count']:<8} {b['frequency']:<14.8g} {b['binomial_SE']:<15.8g} "
                           f"{b['wilson95_low']:<15.8g} {b['wilson95_high']:<15.8g} {b['reference_probability']:<15.8g} "
                           f"{b['reference_standardized_difference']:.3f}")
            out += [f"Empirical TV from reference: {info['empirical_total_variation_from_reference']:.6g}",
                    f"Mean3^excess: {info['mean_p_to_excess']:.6g} (sampleSE {info['mean_p_to_excess_SE']:.6g}); reference2.", ""]
    out += ["DIVISIBILITY CONTRASTS (N differing by1; not an isolated causal test)", "="*76]
    for c in results["divisibility_contrasts"]:
        out.append(f"N={c['divisible_N']} minusN={c['neighbor_N']}, lambda={c['lambda']}, excess0: "
                   f"difference={c['difference']:.6g}, SE={c['SE']:.6g}, z={c['z']:.3f}")
    out += ["", "INTERPRETATION LIMITS", "="*76,
            "These are finite-size histograms. No convergence rate is available in the proposed theorem.",
            "Agreement is not proof of the limiting law; a finite-N discrepancy is not by itself an asymptotic counterexample.",
            "Rare excess>=3 bins have low expected counts; zero observations do not establish zero probability.",
            "The reference distributional claim requires the separate determinacy review; the supplied scalar note proves moments.",
            "No old full-kernel algorithm, code, tests, source, or manuscript is edited.", "",
            "ARTIFACTS", "="*76,
            "samples.csv: full paired raw nullities/excesses for every graph.",
            "histograms.csv: all tabulated bins, counts, binomialSE, Wilson95 and reference probabilities.",
            "results.json: complete structured results, seeds, pilot, timing, contrasts and environment.",
            "observed-vs-symmetric-law.pdf/.png: standard Matplotlib scientific figure.",
            "The figure pools excess>=4; the tables preserve every observed bin and additional zero bins.",
            f"Sampling elapsed seconds: {results['sampling_elapsed_seconds']:.3f}",
            f"Pilot excluded from study; counts selected before main sampling: {results['actual_fixed_targets']}."]
    (HERE/"REPORT.txt").write_text("\n".join(out)+"\n")


def main():
    start = time.monotonic()
    validation = validate_new_rank_routine()
    constant, probabilities = reference_law(P)
    pilot_rng = np.random.default_rng(SEED+104729)
    pilots = []
    for N, target in zip(SIZES, PLANNED_COUNTS):
        tick = time.monotonic()
        for _ in range(12):
            a = sample_k4_lift(N, pilot_rng)
            assert np.array_equal(a, a.T) and np.all(a.sum(axis=1) == 3)
            assert np.all(np.diag(a) == 0)
            excess_pair(a)
        pilots.append({"N": N, "excluded_samples": 12,
                       "seconds_per_graph_two_ranks": (time.monotonic()-tick)/12})
    estimated = sum(x["seconds_per_graph_two_ranks"]*m for x, m in zip(pilots, PLANNED_COUNTS))
    factor = min(1.0, 240/max(estimated, .001))
    targets = [max(50, int(m*factor)//50*50) for m in PLANNED_COUNTS]
    streams = np.random.SeedSequence(SEED).spawn(len(SIZES))
    rngs = [np.random.default_rng(child) for child in streams]
    observations = {N: [] for N in SIZES}
    print(json.dumps({"stage": "sampling", "pilot_estimated_seconds": estimated,
                      "fixed_targets": targets}), flush=True)
    sampling_start = time.monotonic()
    last_progress = sampling_start
    with (HERE/"samples.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["N", "sample", "nullity_lambda0", "excess_lambda0", "nullity_lambda2", "excess_lambda2"])
        unfinished = True
        while unfinished:
            unfinished = False
            for N, target, rng in zip(SIZES, targets, rngs):
                for _ in range(min(50, target-len(observations[N]))):
                    a = sample_k4_lift(N, rng)
                    x0, x2 = excess_pair(a)
                    observations[N].append((x0, x2))
                    writer.writerow([N, len(observations[N]), x0+1, x0, x2+3, x2])
                unfinished |= len(observations[N]) < target
            if time.monotonic()-last_progress > 12:
                print(json.dumps({"stage": "sampling", "counts": {str(N): len(observations[N]) for N in SIZES},
                                  "elapsed_seconds": time.monotonic()-sampling_start}), flush=True)
                last_progress = time.monotonic()
                handle.flush()
    groups = []
    for N, target, stream in zip(SIZES, targets, streams):
        values = np.asarray(observations[N], dtype=np.int64)
        assert len(values) == target
        groups.append({"N": N, "samples": target, "seed_spawn_key": list(stream.spawn_key),
                       "shifts": {"0": summarize(values[:, 0], probabilities),
                                  "2": summarize(values[:, 1], probabilities)}})
    contrasts = []
    for ga, gb in [(groups[0], groups[1]), (groups[2], groups[3])]:
        for label in ["0", "2"]:
            ba, bb = ga["shifts"][label]["bins"][0], gb["shifts"][label]["bins"][0]
            difference = ba["frequency"]-bb["frequency"]
            se = math.hypot(ba["binomial_SE"], bb["binomial_SE"])
            contrasts.append({"divisible_N": ga["N"], "neighbor_N": gb["N"],
                              "lambda": int(label), "excess": 0, "difference": difference,
                              "SE": se, "z": difference/se if se else 0.0})
    results = {"model": "independent uniform permutation N-lift of K4",
               "prime": P, "seed": SEED, "bit_generator": "PCG64 via SeedSequence.spawn",
               "planned_counts": PLANNED_COUNTS, "actual_fixed_targets": targets,
               "pilot": pilots, "pilot_excluded_from_histograms": True,
               "pilot_estimated_sampling_seconds": estimated,
               "sampling_elapsed_seconds": time.monotonic()-sampling_start,
               "validation": validation,
               "reference": {"formula": "pi_k=C/prod_(j=1)^k(3^j-1)",
                             "normalizing_constant": constant, "probabilities": probabilities},
               "groups": groups, "divisibility_contrasts": contrasts,
               "environment": {"python": platform.python_version(), "numpy": np.__version__,
                               "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
               "total_elapsed_before_plot_seconds": time.monotonic()-start}
    (HERE/"results.json").write_text(json.dumps(results, indent=2)+"\n")
    with (HERE/"histograms.csv").open("w", newline="") as handle:
        fields = ["N", "lambda", "samples"]+list(groups[0]["shifts"]["0"]["bins"][0])
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for group in groups:
            for label, info in group["shifts"].items():
                for b in info["bins"]:
                    writer.writerow({"N": group["N"], "lambda": label, "samples": group["samples"], **b})
    make_figure(results, probabilities)
    write_report(results)
    print(json.dumps({"stage": "complete", "counts": targets,
                      "sampling_seconds": results["sampling_elapsed_seconds"],
                      "summary": [{"N": g["N"], "shift": label,
                                   "hist": info["histogram"], "TV": info["empirical_total_variation_from_reference"]}
                                  for g in groups for label, info in g["shifts"].items()]}), flush=True)


if __name__ == "__main__":
    main()
