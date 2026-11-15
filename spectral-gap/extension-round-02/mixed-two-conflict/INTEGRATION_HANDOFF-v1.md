# Two-conflict integration and frontier handoff

Revision 1. November 15, 2026 UTC. Maintained manuscript files remain unchanged by this task.

## TeX candidate

`integration-candidate-v1.tex`, SHA256 `cb4313258b9ac9e0e0dd8b458dc5a0a585678aba9349a3d9d27c792a7ad1e93f`, is a compact integration of frozen `proof-v1.md`, SHA256 `07c2aa5a4907a309546180835fe47e5a5301f352ed55bbd9e15aaf7dfa41a952`.

Insert it after the one-conflict subsection and immediately before `\subsection{Scalar consequences and the optimal prefactor}` in the manuscript mixed section. It reuses the existing affine and kernel lemmas, keeps all four selected-support cases and the attaining construction, and adds labels `thm:twoconflict`, `eq:twoconflictexact`, `eq:twoconflictgeneral` and `eq:twoselected`.

The full manuscript compiled twice in an isolated copy without box warnings, undefined references or duplicate labels. Rendered pages 8 through 10 were visually inspected. The temporary PDF is `/tmp/spectral-mixed-two-layout/manuscript/main.pdf`. The maintained inputs copied for that check had these hashes:

- `main.tex`: `5f60336367a9c3e00879f3c53e9b0806a16a917e24b0b36a3ba6d61b286d4051`.
- `sections/mixed.tex`: `b822c896bf25d0d00b717e34bd48c2b743e0ad282e57a30c8cc27daef0589ab1`.

These are layout provenance, not a restriction on unrelated later edits. Integration should use the independent review of the exact frozen proof.

## General clique conjecture

The separate `clique-counterexample-v1.md`, SHA256 `2401b800d41a055699e691e62f967db2ac814321079a0c90fae368d2f2ccf32d`, refutes the proposed general clique envelope. At $n=a=b=8,h=0$, four disjoint same-row pairs give $8^8\mathbb EX=1121/105>7$, the single-row clique value. The exact excess is $386/105$.

`check_clique_counterexample.py`, SHA256 `b9c2ade7cca9a8bda6a8927441e94b15740d18a9416051f1155307e3c4289448`, independently enumerates all 40,320 permutations and obtains the integer sum 430,464. It also evaluates the compatible-subset formula exactly. Both checks passed. This is an obstruction to the broader guess and does not alter MIX2-1 or its general upper bound.

No further exploration of the arbitrary-$b$ exact envelope was pursued. The packet does not claim the smallest counterexample or historical firstness.
