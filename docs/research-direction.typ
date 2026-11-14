#import "@preview/unequivocal-ams:0.1.2": ams-article

#show: ams-article.with(
  title: [Randomized sketches for matrix multiplication],
  authors: (),
  abstract: none,
)

#set document(description: "Research question, definitions, and baseline algorithms for spectral approximation of a matrix product.")
#set math.equation(numbering: none)
#show link: set text(font: "New Computer Modern")
#set table(inset: (x: 4pt, y: 5pt), stroke: 0.35pt)

= Problem

Given dense real matrices $A in RR^(n times m)$ and $B in RR^(m times p)$, write $M = A B$. Assume $m << min(n,p)$. Costs count arithmetic operations.

The *spectral norm* of an error matrix $E$ is
$ norm(E)_2 = max_(norm(v)_2 = 1) norm(E v)_2. $
It is the largest error on any unit vector. Given an absolute tolerance $epsilon > 0$ and a failure probability $delta in (0,1)$, the goal is to return $C$ with
$ Pr[norm(C - A B)_2 <= epsilon] >= 1 - delta. $
This must hold for every fixed input pair; probability is over the algorithm's random choices.

A *sketch* represents the answer by factors $X in RR^(n times r)$ and $Y in RR^(p times r)$, so $C = X Y^T$. Its width $r <= m$ is the number of columns per factor. *Construction* finds the factors; *expansion* forms the full answer. Let $sigma_j(M)$ be the $j$-th largest singular value.

Define $D = n+p$, the input size $I = m(n+p)$, and $F = norm(A)_F norm(B)_F$, where $norm(A)_F^2 = sum_(i,j) A_(i j)^2$.

= Co-Occurring Directions

*Co-Occurring Directions (COD)* is a deterministic sketching algorithm [2]. Write $a_i$ for column $i$ of $A$ and $b_i$ for the transpose of row $i$ of $B$. Then
$ A B = sum_(i=1)^m a_i b_i^T. $
COD processes these $m$ pairs in one pass. It maintains $U in RR^(n times ell)$ and $V in RR^(p times ell)$, whose product $U V^T$ approximates this sum.

*The width $ell$ is the number of column slots in each COD factor.* It stores $(n+p)ell$ numbers and has rank at most $ell$. This capacity differs from the target rank $r$ below.

COD inserts each pair into empty slots. When full, it uses QR factorizations and a singular value decomposition (SVD) to find the directions of its current product. It subtracts a common threshold from the singular values, setting negative results to zero and freeing at least half the slots. Thus its factors depend on the data.

For even $ell$, the original bound is
$ norm(A B - U V^T)_2 <= (2 F)/ell. $
So an even $ell >= 2 F/epsilon$ suffices, with no failure probability. If this requires $ell >= m$, keeping $A$ and $B^T$ already gives an exact width-$m$ representation. COD is useful for compression when $ell < m$. Its construction time is $O(m(D+ell)ell)$ [2]; later work gives sharper error bounds [3].

= Known algorithms

Let $theta in (0,1)$ be relative-error slack, separate from absolute tolerance $epsilon$. The notation $tilde(O)$ hides logarithmic factors in dimensions, $1/theta$, and $1/delta$. First consider conventional arithmetic.

The *QR and core SVD* method writes
$ A = Q_A R_A, quad B^T = Q_B R_B, quad H = R_A R_B^T. $
QR separates orthonormal directions ($Q$) from coefficients ($R$); SVD orders directions by singular value. Since $M = Q_A H Q_B^T$, an SVD of the $m times m$ matrix $H$ gives optimal rank-$r$ factors.

A faster route forms the Gram matrices $A^T A$ and $B B^T$, then uses small-core linear algebra and lifts the retained directions.

*Block Krylov* applies $M v = A(B v)$ and $M^T u = B^T(A^T u)$ repeatedly, with $tilde(O)(1/sqrt(theta))$ iterations [4, 6]. Failure probability $delta$ adds logarithmic overhead [4, Appendix A]. Fall back to the core method if the basis becomes too large.

Expansion adds $O(n p r)$ to a rank-$r$ construction. COD expansion costs $O(n p ell)$.

= Research question

*Find a randomized algorithm whose total time improves, including the full output.* Given $A,B,r,theta,delta$, preserve the published Krylov guarantee
$ Pr[norm(A B-X Y^T)_2 <= (1+theta)sigma_(r+1)(A B)] >= 1-delta, $
for every fixed input pair, without a spectral-gap assumption. Return the factors *and explicitly form* $C=X Y^T$.

Let $w=9/4$ be a square-multiplication exponent bound from a 2026 preprint [9], and $zeta>0$ arbitrary fixed exponent slack. Seek
$ T_("build")=tilde(O)(I r+m^(w+zeta)), quad
  T_("total")=T_("build")+O(n p r). $
The terms pay for input processing and lifting, fast core linear algebra [5], and expansion. Accuracy and confidence should enter logarithmically. These are unproved targets.

*Construction comparison.* Let $T_("MM")(a,b,c)$ bound exact $a times b$ by $b times c$ multiplication. The Gram cost is $G=T_("MM")(m,n,m)+T_("MM")(m,p,m)$. QR and the Gram route attain error $sigma_(r+1)(A B)$ deterministically; Krylov and the target have the displayed $(1+theta)$ guarantee with probability at least $1-delta$.

#block[
  #set text(size: 8.7pt)
  #set par(first-line-indent: 0pt)
  #table(
    columns: (48mm, 1fr),
    table.header([*Method*], [*Construction time*]),
    [Known conventional QR + SVD], [$tilde(O)(D m^2+m^3)$],
    [Known block Krylov], [$tilde(O)(I r/sqrt(theta)+D r^2/theta)$],
    [Known fast Gram + core SVD], [$tilde(O)(G+I r+m^(w+zeta))$],
    [*Proposed target*], [*$tilde(O)(I r+m^(w+zeta))$*],
  )
]

The target removes the exact Gram cost $G$, and removes Krylov's polynomial accuracy factors while paying for a small core. It improves these bounds only in suitable regimes. Fast core SVD is already available [5]; obtaining an adequate core more cheaply is the new step. Section 5 includes expansion in the comparison.

= Full output comparison

Here is a regime where that target would reduce the *total* exponent. Let $N$ grow, and choose
$ n=p=N, quad m=ceil(N^(8/9)), quad r=1, quad theta=1/m, quad delta=1/100. $
The inputs are $N times m$ and $m times N$; the output has $N^2$ entries. The proposed guarantee is
$ Pr[norm(C-A B)_2 <= (1+1/m)sigma_2(A B)] >= 99/100. $
*Conversion to absolute error.* The guarantee implies error at most $epsilon$ when
$ (1+1/m)sigma_2(A B)<=epsilon
  quad arrow.l.r quad sigma_2(A B)<=epsilon/(1+1/m). $
On the successful event, $norm(C-A B)_2 <= (1+1/m)sigma_2(A B)<=epsilon$, so $Pr[norm(C-A B)_2<=epsilon]>=99/100$.

This is an *additional assumption for the rank-one example*. Arbitrary inputs need not satisfy it. Even the best rank-one answer needs $sigma_2(A B)<=epsilon$; the factor $1+1/m$ leaves room for relative-error slack. Full rank $m$ is allowed, but the product must admit a rank-one approximation at this tolerance. General inputs need a larger or adaptive width, including its selection cost. No bound on $F/epsilon$ is assumed.

The complete cost of the proposed algorithm would be
$ T_("build") = tilde(O)(N^(17/9)+N^(2+(8/9)zeta)), quad
  T_("expand")=O(N^2). $
The target is $N^(2+o(1))$, meaning $O(N^(2+eta))$ for every fixed $eta>0$ after choosing the slack. This matches the exponent needed to write the output.

The table includes expansion in *every row*. Exponents suppress logarithms and arbitrarily small exponent slack. The fast rows follow from [5, 9].

#block[
  #set text(size: 8.8pt)
  #set par(first-line-indent: 0pt)
  #table(
    columns: (55mm, 45mm, 1fr),
    table.header([*Algorithm*], [*Total time*], [*Exponent*]),
    [Conventional exact multiplication], [$N^(26/9+o(1))$], [$approx 2.8889$],
    [Conventional block Krylov], [$N^(7/3+o(1))$], [$approx 2.3333$],
    [Fast exact rectangular multiplication], [$N^(625/288+o(1))$], [$approx 2.1701$],
    [Fast Gram matrices + core SVD], [$N^(169/81+o(1))$], [$approx 2.0864$],
    [*Proposed fast-core target*], [*$N^(2+o(1))$*], [*$2$*],
  )
]

The Gram route attains optimal rank-one error deterministically; exact multiplication has zero error. The proposed target saves a factor $N^(7/81-o(1))$ over the best of these named routes, including output expansion.

*Derivation of the fast comparisons.* Reference [9] gives the rectangular exponent bound
$ omega(1,k,1) <= 1+k+1/(4k) quad (k>=1/2), $
where $omega(1,k,1)$ concerns an $s times s^k$ by $s^k times s$ product. Substituting $k=8/9$ gives the exact-product exponent $625/288$. To form either Gram matrix, use base $s=m$ and $k=9/8$: its cost is $m^(169/72+o(1))=N^(169/81+o(1))$. The core costs $m^(9/4+o(1))=N^(2+o(1))$, lifting costs $O(N m)$, and expansion costs $O(N^2)$.

Cubic core processing would cost $N^(8/3+o(1))$ and miss the target. These are upper bounds for named routes. Proving the new construction and checking novelty against other product-aware methods remain open tasks.

= Why singular values appear

Singular values measure how strongly $M$ acts along independent directions, in decreasing order. A width-$r$ product can retain only $r$ directions. Keeping the largest $r$ gives the smallest possible error:
$ min_("rank"(C) <= r) norm(M-C)_2 = sigma_(r+1)(M). $
This limit applies to every algorithm [1]. With singular values $10, 1, 0.01$, the best rank-one error is $1$ and the best rank-two error is $0.01$. No rank-one answer achieves error $0.1$.

Singular values need not be supplied as input. The necessary width is the number of singular values strictly larger than $epsilon$; $sigma_(r+1)(M)<=epsilon/(1+theta)$ suffices for our guarantee. An adaptive algorithm must find and certify a sufficient rank. Width $m$ allows exact representation.

= Possible approach

+ Sketch the tall inputs while preserving their interaction in a small matrix.
+ Refine directions in that matrix, avoiding repeated passes over all inputs.
+ Recover $X,Y$ and prove the spectral-error guarantee.
+ Certify adaptive rank selection; keep total failure probability at most $delta$.

Ordinary randomized SVD through $A(B v)$ is known. Generic matrix-vector access has strong lower bounds [7, 8], so exploit the separate factors $A,B$. A first result may need extra assumptions, but it must improve the total bound in an explicit regime such as the one above.

= References

#set text(size: 8.5pt)
#set par(first-line-indent: 0pt, leading: 0.4em, spacing: 0.5em)
[1] #link("https://arxiv.org/abs/0909.4061")[Halko, Martinsson and Tropp (2011). Finding Structure with Randomness.]

[2] #link("https://proceedings.mlr.press/v54/mroueh17a.html")[Mroueh, Marcheret and Goel (2017). Co-Occurring Directions Sketching for Approximate Matrix Multiply.]

[3] #link("https://arxiv.org/abs/2009.02553")[Luo et al. (2021). Revisiting Co-Occurring Directions.]

[4] #link("https://arxiv.org/abs/1504.05477")[Musco and Musco (2015). Randomized Block Krylov Methods.]

[5] #link("https://arxiv.org/abs/math/0612264")[Demmel, Dumitriu and Holtz (2007). Fast Linear Algebra Is Stable.]

[6] #link("https://arxiv.org/abs/2508.06486")[Chen et al. (2025). Does block size matter in randomized block Krylov low-rank approximation?]

[7] #link("https://arxiv.org/abs/2304.03191")[Bakshi and Narayanan (2023). Krylov Methods are (nearly) Optimal for Low-Rank Approximation.]

[8] #link("https://arxiv.org/abs/2609.35840")[Zhang et al. (2026, preprint). Matrix-Vector Complexity of Low-Rank Approximation.]

[9] #link("https://arxiv.org/abs/2610.30054")[Amanov, van den Berg and Zuiddam (2026, preprint). Multiplying matrices via polynomials: exposition and barriers.]
