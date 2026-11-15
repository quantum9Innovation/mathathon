# Supporting finite-check evidence

This small supplement preserves three review checkers, their saved results, the three associated review texts and the files needed by the two-conflict checker's hash verification. It supports the mixed-product results in the accompanying report. It contains no external paper downloads or complete historical research archive.

The three checker sources are byte-for-byte copies. Their original locations and hashes appear in [SOURCE_PROVENANCE.json](SOURCE_PROVENANCE.json). No mathematical code or path adapter was introduced. The original relative layout is retained so that the two-conflict checker produces the same path fields as before.

## Fresh replay

[REPLAY_RECEIPT.json](REPLAY_RECEIPT.json) records a successful fresh replay of all three original checkers. Every JSON field and every output report byte matched the saved results. No fields were excluded from comparison. The replay also checked the identities of all 18 preserved files before and after execution.

Run from this directory on a POSIX system with Python 3:

```bash
python3 replay.py --receipt /tmp/problem21-fresh-replay.json
```

The wrapper creates a fresh temporary directory and runs the three checkers sequentially. Each subprocess has a 300-second wall limit, a 300-second CPU limit and a 2 GiB address-space limit. It deletes only the copied expected report before each run, so success requires a newly generated result. It removes the temporary working copy afterward. The requested receipt is the only persistent output.

The replayed programs require only the Python standard library. They use integers and `fractions.Fraction` for exact arithmetic, direct permutation enumeration, finite coefficient recurrences and fixed-seed sampling. No floating-point comparisons, external services or third-party mathematical libraries are used by these three checkers. The broader report's other computational tools are outside this supplement's replay scope.

## Checked domains

A factor is encoded by `(color, row, column, p, q)` and denotes `(M[row,column] - 1/n)^p M[row,column]^q`. The distinct colored support size is `a`. The counts `h` and `b` distinguish consistent and conflicting centered singletons. Products across colors use independent permutations. Direct expectations enumerate every permutation within each color and multiply the resulting exact expectations.

### Base mixed envelope

Source: [mixed-by-saddle-checks-v1.py](extension-round-02/reviews/mixed-by-saddle-checks-v1.py). Saved output: [mixed-by-saddle-check-results-v1.json](extension-round-02/reviews/mixed-by-saddle-check-results-v1.json). Review: [mixed-by-saddle-v1.md](extension-round-02/reviews/mixed-by-saddle-v1.md).

| Family | Exact checked domain | Count |
| --- | --- | --- |
| Depleted moments | `2 <= n <= 8`, every `0 <= s <= n` and `0 <= j <= n-s` | 161 |
| Color merging | `2 <= n <= 14`, every permitted four-index combination | 11,622 |
| Moment and kernel monotonicity | `2 <= n <= 14`, every adjacent admissible depletion comparison | 559 each |
| Affine weights | `2 <= n <= 40`, `0 <= p <= 40`, `0 <= q <= 3`, `p+q >= 1` | 6,357 |
| Attaining products | `2 <= n <= 6`, `1 <= a <= n`, `0 <= h <= a` | 75 |
| Sampled original products | `2 <= n <= 5`, one to three colors, 80 samples per size/color pair, `1 <= a <= n` | 960 |

The sampled exponent pairs are `(0,1)`, `(1,0)`, `(2,0)`, `(3,0)`, `(8,0)`, `(11,0)`, `(2,3)` and `(5,2)`. The sample seed is 743812.

### One-conflict envelope and general upper bound

Source: [one-conflict-v1-checks.py](extension-round-02/reviews/one-conflict-v1-checks.py). Saved output: [one-conflict-v1-check-results.json](extension-round-02/reviews/one-conflict-v1-check-results.json). Review: [one-conflict-v1-review.md](extension-round-02/reviews/one-conflict-v1-review.md).

The checker enumerates all colored supports of sizes `2 <= a <= n` in two colors at `n=2,3`, with exponent pairs from `(0,1)`, `(1,0)`, `(2,0)`, `(3,0)` and `(1,2)`. At `n=4`, it enumerates all one-color supports of sizes 2 through 4 with raw or centered-singleton factors. Products with `b=0` are skipped. The retained exhaustive families comprise 20,224 two-color cases with `b=1`, 3,116 with `b>=2`, 11,456 one-color cases with `b=1` and 17,052 with `b>=2`.

With seed 842019, the program generates 2,000 three-color samples at `n=5` and 1,200 at `n=6`. Their supports have sizes 2 through `n`. The exponent choices add `(5,0)`, `(7,0)`, `(2,3)`, `(4,1)` and `(0,4)` to the preceding five choices. Of these samples, 299 have `b=1` and 20 have `b>=2`. Thus the checked original-product total is 52,167. The original-product total excludes the separately tabulated attainment and illustrative evaluations.

Further checks cover all 84 attainment triples `2 <= n <= 8`, `2 <= a <= n`, `0 <= h <= a-2`, all 679 kernel-difference identities for `2 <= n <= 15`, `0 <= s < n`, `0 <= j < n-s`, and all 161 directly enumerated depleted moments through `n=8`.

### Two-conflict envelope and general upper bound

Source: [two-conflict-v1-checks.py](extension-round-02/reviews/two-conflict-v1-checks.py). Saved output: [two-conflict-v1-check-results.json](extension-round-02/reviews/two-conflict-v1-check-results.json). Review: [two-conflict-v1-review.md](extension-round-02/reviews/two-conflict-v1-review.md).

The exhaustive size, support and exponent families are the same small families specified for the one-conflict checker, retaining only `b>=2`. They yield 3,116 two-color cases at `n=2,3` and 17,052 one-color cases at `n=4`.

With seed 942081, the program generates 2,400 three-color samples at `n=5` and 1,800 at `n=6`, using the same ten exponent choices as the one-conflict sample. Of these, 33 have `b>=2`. Three targeted shared-neighbor and color examples bring the checked original-product total to 20,204. These checks include 18,833 full-support cases, 1,653 multicolor cases and 1,976 repeated or mixed-power cases. Those categories overlap.

The program checks all selected subsets of the remaining support for each retained original-product case, totaling 63,916 selected-support checks. All four compatible cases and the incompatible case occur. All 84 attainment triples `2 <= n <= 8`, `2 <= a <= n`, `0 <= h <= a-2` attain the claimed negative value exactly.

The two-conflict checker also verifies the original packet manifest, its seven entries and the integration-candidate hash. This requires retaining the earlier base and one-conflict proofs, the two-conflict proof and small administrative records, and the original author's checker and saved output. That additional author checker is present only as a hashed dependency and is not run by `replay.py`. Its stored counts are not fresh replay results.

## Interpretation and provenance limits

The review texts record separately assigned internal mathematical reconstructions, with their prior exposure described. They are not external human peer review or end-to-end formal verification. This fresh replay repeats the preserved programs in new processes. It is not a new independent implementation of their mathematical checks.

Every finite count above refers to the stated domain. Sampled families are not exhaustive. The three checkers have overlapping domains, so their counts must not be added as if they represented disjoint products. The unrestricted theorems depend on written proofs, not on finite enumeration.

Historical packet status fields are preserved, including the two-conflict manifest's status before its later accepted review. Existing source and review files have not been rewritten to change their historical state. [ORIGINAL_SOURCE_PRESERVATION.json](ORIGINAL_SOURCE_PRESERVATION.json) records a separate comparison with the original workspace sources after the replay. [SUPPLEMENT_MANIFEST.json](SUPPLEMENT_MANIFEST.json) identifies this delivered supplement.
