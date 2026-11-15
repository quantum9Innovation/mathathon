# A limit of the clique-extremizer guess

Revision 1. November 15, 2026 UTC. This note is separate from frozen MIX2-1. It refutes a proposed generalization and changes no accepted theorem.

## 1. Proposed generalization

With $b$ inconsistent centered singletons, $h$ consistent centered singletons and $r=a-h-b$ other cells, a natural candidate for the exact absolute envelope is

\[
n^{-a}\bigl(bK_{h,r+1}-K_{h,r}\bigr).
\tag{1}
\]

A row containing all $b$ inconsistent centered cells, with every other requested cell compatible with that row and with the others, attains this expression. This does not make it a universal upper bound.

## 2. Exact counterexample

Take one uniform permutation of $[8]$ and the eight cells

\[
(1,1),(1,2),(2,3),(2,4),(3,5),(3,6),(4,7),(4,8).
\]

Center every cell once. Then $n=a=b=8$ and $h=r=0$. Every cell has exactly one same-row conflicting neighbor. Distinct row pairs have disjoint column sets.

Let $A_i=M_{i,2i-1}+M_{i,2i}$ for $1\le i\le4$. Because the two indicators in each row are mutually exclusive,

\[
8^2(M_{i,2i-1}-1/8)(M_{i,2i}-1/8)=1-8A_i.
\]

For any set $J$ of $j$ rows, expanding its $A_i$ gives $2^j$ compatible choices of prescribed matches. Therefore

\[
\mathbb E\prod_{i\in J}A_i=\frac{2^j}{(8)_j}.
\]

Consequently the full centered product $X$ satisfies

\[
8^8\mathbb EX
=\sum_{j=0}^4\binom4j(-2)^j\frac{8^j}{(8)_j}
=\frac{1121}{105}.
\tag{2}
\]

The proposed bound (1) has scaled value $8K_{0,1}-K_{0,0}=7$. Its shortfall is

\[
\frac{1121}{105}-7=\frac{386}{105}>0.
\]

Thus a collection of disjoint conflicting pairs can exceed the single-row clique. The exact $b=2$ envelope does not extend to arbitrary $b$ by replacing its coefficient two with $b$.

## 3. Independent finite check and scope

Direct enumeration of all $8!=40320$ permutations gave the integer sum

\[
\sum_{\sigma\in S_8}\prod_{i=1}^4
(8M_{i,2i-1}-1)(8M_{i,2i}-1)=430464.
\]

Dividing by $40320$ gives $1121/105$, independently matching (2). The check uses exact integers and rationals. Its source is `check_clique_counterexample.py`.

The pattern was proposed by the coordinator before this calculation. The algebra and permutation enumeration were checked separately here. No independent-discovery claim, smallest-counterexample claim, exact envelope for $b>2$, or historical firstness claim is made.
