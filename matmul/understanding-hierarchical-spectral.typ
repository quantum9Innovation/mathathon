// typst compile docs/understanding-hierarchical-spectral.typ
// Uses only built-in Typst features.

#set document(
  title: "Spectral approximation of a matrix product",
  description: "Explanatory notes on hierarchical absolute pencils, their error guarantee, and their running time.",
)
#set page(
  paper: "us-letter",
  margin: 1in,
  numbering: "1",
  number-align: center,
)
#set text(font: "New Computer Modern", size: 11pt)
#set par(justify: true, leading: 0.55em, spacing: 0.65em)
#set heading(numbering: "1.")
#show heading.where(level: 1): set text(size: 12pt)
#set math.equation(numbering: none)
#set table(stroke: none, inset: (x: 5pt, y: 5pt))

#align(center)[
  #text(size: 17pt)[Spectral approximation of a matrix product]

  Notes on #emph[Hierarchical absolute pencils for block spectral
  approximation of factored products]

  14 November 2026
]
#v(0.6em)

The paper [H] studies how to compress the product of two matrices without
first computing the product in full. It returns a matrix of rank at most
$r$, with error nearly as small as any matrix of that rank could achieve.
Earlier algorithms already give this accuracy. The paper's contribution
is a better asymptotic running time for a particular range of dimensions,
ranks, and accuracies. These notes explain the approximation problem
first, then the time comparison and the construction.

= Multiplication and compression

Let $A$ have $n$ rows and $m$ columns, and let $B$ have $m$ rows and $p$
columns. Their product $M=A B$ has $n$ rows and $p$ columns. Each entry
is the sum of products from one row of $A$ and one column of $B$. For example,

$
  mat(1, 2; 3, 4) mat(5, 6; 7, 8)
  = mat(19, 22; 43, 50).
$

The top-left entry is $1 dot 5+2 dot 7=19$. Computing all entries this
way takes $O(n m p)$ arithmetic operations. Faster exact algorithms
reorganize the computation, and are included in the comparison below.

A matrix also represents a linear transformation of a vector, which is
a list of numbers. The product means applying $B$ first and then $A$:
$M x=A(B x)$. Knowing the separate factors therefore lets us apply $M$
to a vector without storing all of $M$.

The approximation has the form

$ C=X Y^T, quad X in RR^(n times r), quad Y in RR^(p times r). $

The transpose $Y^T$ exchanges the rows and columns of $Y$. To compute
$C x$, we first compute the $r$ coordinates $Y^T x$, then combine the
columns of $X$ using those coordinates. All resulting vectors lie in the
space spanned by the $r$ columns of $X$. Thus $C$ has rank at most $r$:
it can produce at most $r$ independent output directions.

The two factors store $(n+p)r$ numbers, whereas a full matrix stores
$n p$. The original factors $A,B$ already give an exact representation
of width $m$. The compression problem is to find a useful approximation
with $r<m$. The algorithm also explicitly forms the full matrix $C$;
its time bound includes this expansion.

= Spectral error and the best rank-$r$ answer

For an error matrix $E=M-C$, the spectral norm is

$ norm(E)_2=max_(norm(x)_2=1) norm(E x)_2. $

The vector norm is Euclidean length. The spectral norm measures the
largest output error on a unit-length input. An error bound
$norm(M-C)_2<=e$ consequently gives

$ norm(M x-C x)_2<=e norm(x)_2 quad "for every vector" x. $

It controls the worst direction, rather than an average over directions.

#block(breakable: false)[
The singular values $sigma_1(M)>=sigma_2(M)>=dots>=0$ measure the
strengths of a matrix along independent input directions. A singular
value decomposition, or SVD, identifies these directions and their
strengths. Retaining the $r$ largest singular values gives a best
rank-$r$ approximation. Its error is the first discarded singular value [1]:

$ min_("rank"(C)<=r) norm(M-C)_2=sigma_(r+1)(M). $
]

For example, consider $M="diag"(10,4,1)$, which scales three coordinates
by 10, 4, and 1. Keeping just the first coordinate gives
$C_1="diag"(10,0,0)$, with error 4. Keeping the first two gives
$C_2="diag"(10,4,0)$, with error 1. No rank-one or rank-two matrix,
respectively, can do better in spectral norm.

This limit is useful because it separates the loss caused by compression
from the extra loss caused by an algorithm. A rank-one answer can have
large error even when computed optimally. If the singular values are
100, 90, and 80, its error is at least 90.

= The approximation guarantee

Given $A,B$, a target rank $r$, an accuracy parameter $theta>0$, and a
failure probability $delta$, the paper's algorithm returns factors of
width at most $r$ satisfying

$ Pr[norm(A B-X Y^T)_2<=(1+theta)sigma_(r+1)(A B)]>=1-delta. $

Thus $theta$ measures the fractional excess over the best rank-$r$
error. In the example with singular values 10, 4, and 1, setting $r=1$
and $theta=0.05$ gives error at most $1.05 dot 4=4.2$. The 5% is relative
to the optimal compression error, not to the norm of the original matrix.

The inputs are arbitrary fixed matrices. Probability comes from the
algorithm's random sketches and starting vectors. With $delta=0.01$,
at least 99% of runs satisfy the matrix error bound. On each successful
run, the resulting bound holds for every input vector simultaneously.

The guarantee needs no separation between adjacent singular values;
they may coincide. Dependent columns and cancellation between factor
contributions are allowed. If $"rank"(A B)<=r$, the optimal error is
zero and a successful run recovers the product exactly in the paper's
arithmetic model.

For an absolute tolerance $epsilon$, a sufficient rank satisfies

$ sigma_(r+1)(A B)<=epsilon/(1+theta). $

The paper also gives a version that chooses its own rank by trying
increasing widths [H, Corollary 8]. Let $r_epsilon$ be the smallest
nonnegative rank satisfying this inequality. With probability at least
$1-delta$, it returns error at most $epsilon$ and width at most
$2r_epsilon$. The fast time bound described next holds on that same
event when $r_epsilon<=floor(sqrt(m))/2$.

= Running time and comparison with earlier methods

Corollary 7 of [H] gives the following parameter family. Let $n=p=N$,
and choose the inner dimension and accuracy according to

$
  m=N^(a+o(1)), quad a=(3 sqrt(5)-5)/2 approx 0.854102,
  quad theta=(m/N)^(5/2).
$

For every $1<=r<=floor(sqrt(m))$, the algorithm takes $N^(2+o(1))$
arithmetic operations, including all $N^2$ output entries. Confidence
may be fixed, such as 99%, or increased with an inverse-polynomial
failure probability. In powers of $N$, the permitted rank grows through
approximately $N^0.427051$, while $theta$ decreases approximately as
$N^(-0.364745)$. The result therefore allows increasing rank while
getting closer to optimal error.

The exponent describes how work grows with size. For a cost of $N^3$,
doubling $N$ multiplies the work by eight; for $N^2$, by four. In
$N^(2+o(1))$, the additional exponent tends to zero as the dimensions
grow. This notation permits factors larger than powers of logarithms
and does not assert a literal $O(N^2)$ bound.

The following comparison uses the same dimensions, accuracy, and rank
range throughout. Each row includes full output. The exponents suppress
subpolynomial factors.

#figure(
  table(
    columns: (3.05in, 0.85in, 1fr),
    align: (left, right, left),
    table.hline(stroke: 0.5pt),
    table.header([Method], [Exponent], [Error]),
    table.hline(stroke: 0.35pt),
    [Ordinary exact multiplication], [2.854102], [Zero],
    [Fast rectangular exact multiplication], [2.146807], [Zero],
    [Fast Gram matrices and core method], [2.036475], [Meets bound],
    [Block Krylov with fast batched actions], [2.036475], [Meets bound],
    [Hierarchical method], [2], [Meets bound],
    table.hline(stroke: 0.5pt),
  ),
  caption: none,
)

The rectangular multiplication bound comes from [4]. The Gram and
Krylov comparisons are the realizations checked in [H, Section 9 and
Appendix A]. Their leading powers exceed the hierarchical bound by
$0.036474508 dots$. This is a comparison of known upper bounds; it
does not establish a lower bound on every competing algorithm.

Writing $N^2$ entries requires $Omega(N^2)$ operations, so the new bound
attains the smallest possible leading exponent for explicit output in
this family. If an application needs only the thin factors, that output
cost disappears and the relevant comparison changes.

The two closest methods reach the answer in different ways. The Gram
method computes $A^T A$ and $B B^T$, each of size $m times m$. These
record inner products between factor directions and reduce the spectral
problem to a smaller space. Forming these exact matrices is the expensive
part at the stated parameters.

Block Krylov instead begins with random vectors and repeatedly applies
$M$ and $M^T$, using $M v=A(B v)$. Several vectors are processed together
as a block. Musco and Musco [2] proved a spectral approximation guarantee
with about $1/sqrt(theta)$ iterations, up to logarithms. Chen et al. [3]
extended the query analysis to intermediate block sizes. The hierarchy
reduces the number of expensive original-factor actions by preconditioning
a related threshold problem.

Other approximate multiplication results use different benchmarks.
Random sketches often bound error relative to the norms of the factors
[5], which can be large even when the product is small because of
cancellation. Co-Occurring Directions is a deterministic streaming
method, with improved tail-sensitive bounds in later work [6, 7]. Its
memory and error tradeoffs require a separate comparison. Within this
repository, the stochastic method [S] already reaches the same accuracy
envelope at fixed rank; the hierarchy extends it through growing ranks.

= The construction

The algorithm first makes random sketches of the factors. A sketch mixes
and reduces rows while approximately preserving the lengths of vectors
in the relevant subspace. Its distortion $h$ measures the error in this
preservation. The sketches provide approximate Gram matrices at lower
cost than the exact ones. They also identify the inner directions that
contribute to the product and rescale their coordinates. This rescaling,
called whitening, prevents arbitrary scaling of the factors from
controlling the iteration count.

#block(breakable: false)[
The next task is to locate directions whose singular values are too
large to discard. Squared singular values are eigenvalues of $M M^T$.
For a candidate squared cutoff $t$, consider the conceptual matrix

$ K_"ideal"(t)=t I-M M^T. $
]

On a direction with squared singular value $lambda_i$, this matrix acts
by $t-lambda_i$. Its sign tells us which side of the cutoff the direction
lies on. The algorithm implements a corresponding threshold problem in
a space of dimension at most $m$, through the separate factors; it does
not form the displayed $N times N$ matrix. It searches near
$sigma_(r+1)(M)^2$, above which there are at most $r$ singular directions.
The allowed excess error leaves some flexibility for values very close
to the cutoff.

A preconditioner changes coordinates so that this threshold problem is
easier to solve. For a nonzero scalar $k$, dividing by $abs(k)$ leaves
only its sign. Absolute-value preconditioning does the corresponding
rescaling for a symmetric matrix. Exact construction would be expensive,
and eigenvalues near zero require regularization. The paper approximates
the rescaling using sketches and polynomial computations. This is the
meaning of “absolute” in the title. Absolute-value preconditioning itself
predates this work [8].

A coarse sketch is cheap to construct but leaves more refinement to be
done using the original factors. A fine sketch reduces that refinement,
but forming its full Gram matrix can be expensive. The hierarchy uses
several distortions $h_0>h_1>dots>h_L$. It forms full Grams only for
the coarse sketches. At finer levels it stores sketched factors and
applies them to blocks of vectors, improving the preconditioner without
forming the finer Grams. If a sketch would exceed the original factor's
size, it uses that factor directly and includes the cost.

Ignoring logarithms and level constants, this reduces the number of
original-factor block actions from about $theta^(-1/2)$ to about
$sqrt(h_L/theta)$. The intermediate levels add work of their own. The
schedule balances those costs, ending with $h_L$ within fixed factors
of $sqrt(m/N)$ and using $O(log log m)$ levels. Fast rectangular
multiplication processes the blocks efficiently, including when the
rank grows. It is essential to the stated exponent.

Polynomial filters, applied to random starting vectors, then capture
the directions above the threshold. A polynomial filter is evaluated by
repeated matrix actions; it amplifies selected spectral directions
relative to others. Such filtering and principal-component projection
have substantial prior literature [9, 10], as does recursive sketch
preconditioning for other linear-algebra problems [11].

After returning to the original coordinates, let $U$ be an orthonormal
basis for the retained space. Projection onto that space gives

$ C=U(U^T M), quad X=U, quad Y=M^T U=B^T(A^T U). $

Thus the final factors can also be computed through $A$ and $B$.
The error proof bounds the largest action of $M$ outside the retained
space. The main new arguments establish that the successive
preconditioners preserve the needed error bound, even when the matrices
do not share eigenvectors, and that recovery in the original coordinates
avoids an expensive implicit inverse. These are the paper's relaxed
quadratic invariant and carried-preimage identity. The runtime proof
then counts every refinement level, basis computation, and output entry.

= Scope and practical significance

The theorem concerns a particular parameter family. The stronger
original target in the research direction, $m approx N^(8/9)$ and
$theta=1/m$, remains open. A small absolute error also requires the
product to have a small singular-value tail, as explained above.

Exact field operations, positive
scalar square roots, exact comparisons, and Gaussian samples have unit
cost, regardless of representation size. No floating-point stability or
bit-complexity bound is supplied. Intermediate polynomial computations
can grow very large.

The proved constants also prevent a practical interpretation of the
asymptotic gain. The stated schedule accepts its first refinement only
when $N/m>=2^40$, about one trillion. At the optimized power law above,
this requires $N$ of roughly $10^82.53$ or larger. Below that cutoff,
the theorem uses a companion-method fallback and supplies no useful
finite-size speed advantage for that branch [R; H, Section 8]. A stable
implementation and timing experiments would be needed to establish a
practical improvement.

The approximation format can nevertheless be useful at ordinary sizes.
For $N=10,000$ and $r=50$, two factors store one million numbers, while
the full matrix stores one hundred million. At eight bytes per number,
this is 8 MB versus 800 MB. If $sigma_51(A B)=0.01$ and $theta=0.05$,
the error guarantee is $0.0105$: for every vector $x$, the output error
is at most $0.0105 norm(x)_2$. This illustrates the value of the
approximation, without making a timing claim for this algorithm.

The repository contains mathematical review records [R] and a partial
Lean formalization [V]. The complete randomized construction and runtime
theorem remain outside the finished formalization. The literature
comparison supports the improvement over the two checked upper bounds;
global priority remains unconfirmed.

= References

#set text(size: 9.5pt)
#set par(justify: false, leading: 0.45em, spacing: 0.6em)

[H] #link("hierarchical-absolute-spectral.pdf")[Hierarchical absolute pencils for block spectral approximation of factored products.]
Working manuscript, 14 November 2026. Theorems 1–2 and Corollaries 7–8.
Companion: #link("absolute-pencil-spectral.pdf")[Block spectral approximation of a factored product from regularized absolute-value pencils.]

[S] #link("stochastic-product-spectral.pdf")[Variance-reduced spectral approximation of a factored matrix product.]
Working manuscript, 14 November 2026.

[R] #link("hierarchical-mathematical-review.txt")[Mathematical review and practical assessment];
#link("hierarchy-proof-checks.txt")[hierarchy verification record].
[V] #link("../formal/VERIFICATION.txt")[Lean verification coverage map].
Original problem: #link("research-direction.pdf")[Randomized sketches for matrix multiplication].

[1] N. Halko, P.-G. Martinsson, J. Tropp.
#link("https://arxiv.org/abs/0909.4061")[Finding Structure with Randomness: Probabilistic Algorithms for Constructing Approximate Matrix Decompositions.]
SIAM Review, 2011.

[2] C. Musco, C. Musco.
#link("https://arxiv.org/abs/1504.05477")[Randomized Block Krylov Methods for Stronger and Faster Approximate Singular Value Decomposition.]
NeurIPS, 2015.

[3] T. Chen, E. Epperly, R. Meyer, C. Musco, A. Rao.
#link("https://arxiv.org/abs/2508.06486")[Does block size matter in randomized block Krylov low-rank approximation?]
2025; SODA 2026.

[4] A. Amanov, M. van den Berg, J. Zuiddam.
#link("https://arxiv.org/html/2610.30054v1")[Multiplying matrices via polynomials: exposition and barriers.]
Preprint, 2026. Theorems 1.1–1.2 give the square and rectangular multiplication bounds used here.

[5] M. Cohen, J. Nelson, D. Woodruff.
#link("https://arxiv.org/abs/1507.02268")[Optimal Approximate Matrix Product in Terms of Stable Rank.]
ICALP, 2016.

[6] Y. Mroueh, E. Marcheret, V. Goel.
#link("https://proceedings.mlr.press/v54/mroueh17a.html")[Co-Occurring Directions Sketching for Approximate Matrix Multiply.]
AISTATS, 2017.

[7] L. Luo, C. Chen, G. Xie, H. Ye.
#link("https://arxiv.org/abs/2009.02553")[Revisiting Co-Occurring Directions: Sharper Analysis and Efficient Algorithm for Sparse Matrices.]
2021.

[8] E. Vecharynski, A. Knyazev.
#link("https://arxiv.org/abs/1104.4530")[Absolute value preconditioning for symmetric indefinite linear systems.]
SIAM Journal on Scientific Computing, 2013.

[9] Z. Allen-Zhu, Y. Li.
#link("https://proceedings.mlr.press/v70/allen-zhu17c.html")[Faster Principal Component Regression and Stable Matrix Chebyshev Approximation.]
ICML, 2017.

[10] Y. Jin, A. Sidford.
#link("https://arxiv.org/abs/1910.06517")[Principal Component Projection and Regression in Nearly Linear Time through Asymmetric SVRG.]
NeurIPS, 2019.

[11] M. Dereziński, A. Sidford.
#link("https://arxiv.org/abs/2507.11724")[Approaching Optimality for Solving Dense Linear Systems with Low-Rank Structure.]
Preprint, 2025.
