#!/usr/bin/env python3
"""Read-only statistical analysis of the saved rank samples; no new rank runs."""
from pathlib import Path
import csv
import importlib.util
import json
import math
import sys

import numpy as np

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("corank_stats", HERE/"k4_corank_experiment.py")
exp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exp)


def moment_influence(values):
    weights = sorted([3**int(v) for v in values], reverse=True)
    m, total = len(weights), sum(weights)
    mean = total/m
    variance = (sum(w*w for w in weights)-total*total/m)/(m-1)
    top = max(1, math.ceil(.01*m))
    return {"samples": m, "mean": mean, "sample_SE": math.sqrt(max(0, variance)/m),
            "maximum_excess": max(values), "maximum_single_weight": weights[0],
            "maximum_single_contribution_to_mean": weights[0]/m,
            "maximum_single_fraction_of_total_weight": weights[0]/total,
            "top_one_percent_count": top,
            "top_one_percent_fraction_of_total_weight": sum(weights[:top])/total}


def main():
    first = json.loads((HERE/"results.json").read_text())
    follow = json.loads((HERE/"followup/results.json").read_text())
    probabilities = first["reference"]["probabilities"]
    original_twins = {}
    with (HERE/"main-twin-diagnostics.csv").open() as handle:
        for row in csv.DictReader(handle):
            original_twins[(int(row["N"]), int(row["sample"]))] = int(row["adjacent_twin_pairs"])
    records = {}
    for folder, exploratory in [(HERE, False), (HERE/"followup", True)]:
        with (folder/"samples.csv").open() as handle:
            for row in csv.DictReader(handle):
                N, rep = int(row["N"]), int(row["sample"])
                pair_count = int(row["adjacent_twin_pairs"]) if exploratory else original_twins[(N, rep)]
                e0, e2 = int(row["excess_lambda0"]), int(row["excess_lambda2"])
                assert pair_count == 0 or e2 >= 1
                records.setdefault(N, []).append((e0, e2, pair_count, exploratory))
    groups = []
    for N in sorted(records):
        rows = records[N]
        e0, e2, twins = [r[0] for r in rows], [r[1] for r in rows], [r[2] for r in rows]
        no_twins = [r[1] for r in rows if r[2] == 0]
        groups.append({"N": N, "samples": len(rows), "exploratory_followup": rows[0][3],
                       "lambda0": exp.summarize(e0, probabilities),
                       "lambda2": exp.summarize(e2, probabilities),
                       "lambda2_conditional_no_twins": exp.summarize(no_twins, probabilities),
                       "moment_influence_lambda0": moment_influence(e0),
                       "moment_influence_lambda2": moment_influence(e2),
                       "twin_graphs": sum(x > 0 for x in twins),
                       "twin_fraction": sum(x > 0 for x in twins)/len(rows),
                       "mean_twin_pairs": float(np.mean(twins)),
                       "mean_twin_pairs_SE": float(np.std(twins, ddof=1)/math.sqrt(len(rows))),
                       "exact_expected_twin_pairs": 6/N})
    diagnostics = {"reference_pi0": probabilities[0], "groups": groups,
                   "original_sampling_seconds": first["sampling_elapsed_seconds"],
                   "followup_sampling_seconds": follow["sampling_elapsed_seconds"],
                   "all_divisibility_contrasts": first["divisibility_contrasts"]+follow["divisibility_contrasts"],
                   "total_graph_samples": sum(g["samples"] for g in groups),
                   "total_modular_rank_computations": 2*sum(g["samples"] for g in groups)}
    (HERE/"diagnostics.json").write_text(json.dumps(diagnostics, indent=2)+"\n")
    with (HERE/"conditional-no-twins-histograms.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=["N", "conditional_samples"]+list(groups[0]["lambda2"]["bins"][0]))
        writer.writeheader()
        for g in groups:
            info = g["lambda2_conditional_no_twins"]
            for b in info["bins"]:
                writer.writerow({"N": g["N"], "conditional_samples": info["samples"], **b})
    lines = ["FINDINGS: EXACT K4-LIFT FINITE-FIELD CORANK EXPERIMENT", "15 November 2026", "",
             "The lambda2 finite-size discrepancy is large and real, but shrinks as N increases.",
             "No asymptotic counterexample is established. The lambda0 histograms are much closer to the proposed symmetric law.", "",
             "DESIGN", "======",
             "Original fixed sample sizes: N12/13:3000 each; N30/31:600 each.",
             "Exploratory follow-up, selected after those results: N60/61:400 each; N99/100:300 each.",
             f"Total: {diagnostics['total_graph_samples']} independent graph draws; {diagnostics['total_modular_rank_computations']} exact ranks.",
             f"Rank-sampling time: {first['sampling_elapsed_seconds']+follow['sampling_elapsed_seconds']:.3f} seconds total, excluding small pilots and plots.",
             "The original study and follow-up have separate fixed seeds; follow-up counts were fixed using an excluded independent timing pilot.",
             "Both shifts on each graph are paired. Per-bin intervals are pointwise95% Wilson intervals; SE is binomial plug-in SE.",
             "The follow-up and no-twin conditioning are explicitly exploratory.", "",
             f"REFERENCE: pi_k=C/prod_(j=1)^k(3^j-1), C={probabilities[0]:.12g}.",
             "The supplied scalar note proves moments; the TV-law determinacy argument is separately under review.", "",
             "EXCESS-ZERO FREQUENCIES", "=======================",
             "N    m      lambda0 p0(SE)      lambda2 p0(SE)      lambda2 p0|no twins(SE)    no-twin m    twin fraction"]
    for g in groups:
        a, b, c = g["lambda0"]["bins"][0], g["lambda2"]["bins"][0], g["lambda2_conditional_no_twins"]["bins"][0]
        lines.append(f"{g['N']:<4} {g['samples']:<6} {a['frequency']:.5f}({a['binomial_SE']:.5f})   "
                     f"{b['frequency']:.5f}({b['binomial_SE']:.5f})   {c['frequency']:.5f}({c['binomial_SE']:.5f})          "
                     f"{g['lambda2_conditional_no_twins']['samples']:<9} {g['twin_fraction']:.5f}")
    lines += ["", "DESCRIPTIVE CONCLUSIONS", "========================",
              "For lambda2 the unconditional zero-bin frequency rises from .316/.318 at N12/13 to about .59/.597 at N99/100, toward reference .6390.",
              "At N12/13 the empirical total-variation distances are .323/.321; at N99/100 they are .042/.051.",
              "At N30 and above, conditioning out adjacent twins makes the lambda2 zero bin much closer to the reference.",
              "At N12/13 a substantial residual remains even without twins (.499/.480 vs .6390). Twins do not explain the entire small-N discrepancy.",
              "At N99/100 the conditional no-twin zero-bin frequencies are .6393/.6321; these conditional samples still have ordinary binomial uncertainty.",
              "No consistent Nmod3 separation is visible in the paired adjacent-size comparisons. These are not isolated causal tests of residue class.", "",
              "EXACT FINITE-SIZE TWIN MECHANISM", "================================",
              "If u,v have the same closed neighborhood, they are adjacent and e_u-e_v is an exact INTEGER eigenvector at eigenvalue-1, hence lambda2 over F3.",
              "For N>1 this vector is not fiber-constant, so every graph with such a twin has strictly positive lambda2 excess.",
              "Condition on any one of the6N lift edges. Its endpoints' neighbors in each of the two other fibers coincide independently with probability1/N.",
              "Therefore the expected NUMBER of adjacent-twin edges is exactly6/N by linearity, without independence between distinct twin events.",
              "Markov's inequality gives P(any adjacent twin)<=6/N, so this particular obstruction vanishes with N.",
              "This is NOT an exact formula for the probability of any twins, and pi0*(1-6/N) is NOT an exact finite-N corank formula.",
              "Twin groups may contribute several edges at once. The replay counts pairs of identical closed-neighborhood rows.",
              "Every observed twin graph had positive lambda2 excess. Original samples were replayed ONLY to count twins, not to rerun ranks.", "",
              "TWIN EDGE COUNTS", "=================", "N    observed mean(SE)     exact mean6/N    graphs with twins"]
    for g in groups:
        lines.append(f"{g['N']:<4} {g['mean_twin_pairs']:.6f}({g['mean_twin_pairs_SE']:.6f})   "
                     f"{g['exact_expected_twin_pairs']:.6f}       {g['twin_graphs']}/{g['samples']}")
    lines += ["", "EMPIRICAL MOMENT INFLUENCE: lambda2", "===================================",
              "SampleSE describes the observed sample, not a guarantee against unobserved rare high coranks.",
              "N    mean3^e(SE)       max e   max3^e   max contribution to mean   max weight fraction   top1% weight fraction"]
    for g in groups:
        a = g["moment_influence_lambda2"]
        lines.append(f"{g['N']:<4} {a['mean']:.5f}({a['sample_SE']:.5f})   {a['maximum_excess']:<6} "
                     f"{a['maximum_single_weight']:<8} {a['maximum_single_contribution_to_mean']:<25.6g} "
                     f"{a['maximum_single_fraction_of_total_weight']:<21.6g} {a['top_one_percent_fraction_of_total_weight']:.6g}")
    lines += ["", "INTERPRETATION", "===============",
              "This experiment strongly rejects using the limiting PMF as an accurate small-N model for lambda2.",
              "The observed discrepancy shrinks with N and has a concrete finite-size obstruction; it does not falsify a rate-free limiting theorem.",
              "It also does not prove convergence or moment determinacy. Very rare tail bins remain poorly resolved by these sample sizes.",
              "No theorem source, frozen full-kernel code, or old tests were edited/imported. All writes are confined to this new experiment directory.", "",
              "FILES", "======",
              "REPORT.txt and followup/REPORT.txt: full histograms, binomialSE, Wilson95, TV and first moment summaries.",
              "histograms.csv and followup/histograms.csv: every tabulated bin including zero bins.",
              "samples.csv and followup/samples.csv: all raw paired rank results.",
              "conditional-no-twins-histograms.csv: complete posthoc conditional histograms and uncertainty.",
              "diagnostics.json: all influence and conditional calculations.",
              "observed-vs-symmetric-law.pdf/.png plus followup counterparts: PMFs with Wilson intervals.",
              "zero-bin-and-twins.pdf/.png: combined finite-size and twin diagnostic figure.",
              "experiment-independent-audit.txt: independent implementation/statistics review."]
    (HERE/"FINDINGS.txt").write_text("\n".join(lines)+"\n")
    make_diagnostic_figure(groups, probabilities[0])
    print(json.dumps({"groups": len(groups), "samples": diagnostics["total_graph_samples"],
                      "largest_divisibility_contrast_abs_z": max(abs(c["z"]) for c in diagnostics["all_divisibility_contrasts"])}, indent=2))


def make_diagnostic_figure(groups, pi0):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import NullFormatter
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False})
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.3), sharex=True, sharey=True)
    for ax in axes:
        ax.axhline(pi0, color="black", ls="--", lw=1.1, label="Proposed limit π₀ = 0.6390")
        ax.set_xscale("log")
        ax.set_xticks([12, 30, 60, 100], ["12", "30", "60", "100"])
        ax.xaxis.set_minor_formatter(NullFormatter())
        ax.set_ylim(.26, .75)
        ax.set_xlabel("Lift size N (log scale)")
        ax.grid(axis="y", alpha=.18)
    styles = [(axes[0], "lambda0", "#2875aa", "o", "λ = 0"),
              (axes[0], "lambda2", "#c66b23", "s", "λ = 2"),
              (axes[1], "lambda2", "#c66b23", "s", "λ = 2, all graphs"),
              (axes[1], "lambda2_conditional_no_twins", "#358057", "^", "λ = 2, no adjacent twins")]
    for ax, key, color, marker, label in styles:
        x, y, lower, upper = [], [], [], []
        for g in groups:
            b = g[key]["bins"][0]
            x.append(g["N"]);y.append(b["frequency"])
            lower.append(b["frequency"]-b["wilson95_low"])
            upper.append(b["wilson95_high"]-b["frequency"])
        ax.errorbar(x, y, yerr=[lower, upper], color=color, marker=marker,
                    ms=4.5, capsize=2, lw=1, label=label)
    axes[0].set_title("Unconditional excess-zero frequencies")
    axes[1].set_title("Exploratory adjacent-twin diagnostic")
    axes[0].set_ylabel("Probability of zero excess corank")
    for ax in axes:
        ax.legend(frameon=False, fontsize=8.5, loc="lower right")
    fig.text(.5, .01, "95% Wilson intervals. N ≥ 60 is an exploratory follow-up. Conditioning is posthoc; the two right-panel series are dependent.",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, .06, 1, 1))
    fig.savefig(HERE/"zero-bin-and-twins.pdf", bbox_inches="tight")
    fig.savefig(HERE/"zero-bin-and-twins.png", dpi=180, bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    main()
