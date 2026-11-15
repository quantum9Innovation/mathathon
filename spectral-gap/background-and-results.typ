// Build: typst compile spectral-gap/background-and-results.typ
// This document uses no external Typst packages.
#set document(
  title: "Spectral gaps: background and results",
  description: "An introduction to spectral graph theory and the results in the spectral-gap research packet, with emphasis on statements and their meaning.",
)
#set page(paper: "us-letter", margin: 1in, numbering: "1", number-align: center)
#set text(font: "New Computer Modern", size: 11pt)
#set par(justify: true, leading: 0.55em, spacing: 0.65em)
#set heading(numbering: "1.")
#show heading.where(level: 1): set text(size: 12pt)
#show heading.where(level: 2): set text(size: 11pt)
#set math.equation(numbering: none)
#set table(stroke: none, inset: (x: 5pt, y: 5pt))

#align(center)[
  #text(size: 17pt)[Spectral gaps: background and results]

  The random-graph and permutation-product results in the Mathathon packet

  14 November 2026
]
#v(0.6em)

The new material in #link("README.md")[spectral-gap/]
contains two main developments. One concerns how adding a vertex changes
the extreme eigenvalues of a random graph. The other gives exact bounds
and increasingly accurate formulas for products of entries of a random
permutation matrix, quantities used inside spectral-gap arguments.
The package also contains results and corrections for periodic graphs,
directed graphs, hypergraphs, and Cayley graphs.

This document covers those results, together with the earlier theorems
needed to interpret them. The main permutation manuscript supplies sharper
probability estimates, rather than a new bound on the second eigenvalue
of a random graph. Its exact extremal results are the clearest candidates
for distinct new contributions. Several asymptotic formulas overlap with
classical work. The status of each group of results is discussed below.
Proof techniques are mentioned only to explain the objects in a statement.

= Graphs and their matrices

A graph consists of vertices and edges. An undirected edge joins two
vertices without assigning a direction. The degree of a vertex is the
number of its neighbors. A graph is $d$-regular if every vertex has degree
$d$, and connected if every two vertices can be joined by a path. A simple
graph has no loops or repeated edges. Unless specified otherwise, the
random graphs below are simple and undirected.

The adjacency matrix $A$ records the edges: $A_(i j)=1$ when vertices
$i,j$ are adjacent and is zero otherwise. If $x$ assigns a number to each
vertex, then

$ (A x)_i=sum_(j:"j is adjacent to i") x_j. $

Thus matrix multiplication adds the values at neighboring vertices.
An eigenvector is a nonzero assignment satisfying $A x=lambda x$.
It is a pattern that is merely scaled, rather than changed in shape, by
this operation. The scale $lambda$ is its eigenvalue. The collection of
eigenvalues, counted with multiplicities, is the spectrum. Multiplicity
records how many independent patterns have the same eigenvalue.

An undirected graph has a symmetric adjacency matrix, so its eigenvalues
are real. Order them by value:

$ lambda_1>=lambda_2>=dots>=lambda_n. $

For a $d$-regular graph, the constant assignment is an eigenvector with
eigenvalue $d$. This is the largest eigenvalue. If the graph is connected,
it occurs once. More generally, its multiplicity is the number of
connected components.

For example, the triangle has adjacency matrix and spectrum

$ A=mat(0,1,1;1,0,1;1,1,0), quad "spectrum"(A)={2,-1,-1}. $

The constant vector has eigenvalue 2. Every vector whose coordinates
sum to zero has eigenvalue $-1$. Negative eigenvalues are ordinary
features of adjacency matrices, even though their entries are nonnegative.

= What a spectral gap measures

For a connected $d$-regular graph, the top adjacency gap is
$d-lambda_2$. A large gap indicates that a nonconstant pattern cannot
behave almost like the constant one. Combinatorially, this excludes
severe bottlenecks: a large set of vertices cannot be connected to the
rest by disproportionately few edges. Families of sparse graphs with
uniformly good connectivity are called expanders.

The same relation appears in random walks. A step of the walk chooses a
neighbor uniformly. Its matrix is $P=A/d$, whose eigenvalues are
$lambda_i/d$. Repeated steps multiply an eigenvector by successive powers
of that number. Values close to 1 cause slow decay of nonconstant
patterns. Negative values close to $-1$ cause alternation. A lazy walk,
which stays in place with probability one half, has matrix
$(I+P)/2$ and removes that obstruction to mixing.

A bipartite graph has two vertex classes and edges only between classes.
In a connected regular bipartite graph, $-d$ is also an eigenvalue: the
assignment that is $+1$ on one side and $-1$ on the other changes sign
at each step. It must be excluded when measuring an absolute nontrivial
spectral radius. Thus $lambda_2$ by value, the second eigenvalue by
absolute value, and the second eigenvalue after removing structural
modes can describe different quantities.

For irregular graphs the largest adjacency eigenvalue is generally not
a common degree. A useful alternative is the Laplacian
$L=D-A$, where $D$ is the diagonal matrix of vertex degrees. Its quadratic
form is

$ x^T L x=sum_({i,j} in E)(x_i-x_j)^2. $

It measures variation across edges. Its smallest eigenvalue is zero,
and the number of zeros is the number of connected components. The
second-smallest eigenvalue is positive exactly when the graph is
connected. In a regular graph it equals $d-lambda_2 (A)$. The normalized
Laplacian is $I-D^(-1/2)A D^(-1/2)$ when all degrees are positive.
These definitions matter when comparing graphs whose degrees differ.

A spectral gap can also mean an empty interval inside the spectrum,
rather than the distance below the top eigenvalue. Several results in
the packet concern these internal gaps. This use of “spectral” is related
to the matrix-approximation document: for a symmetric matrix, the spectral
norm is the largest absolute eigenvalue. A gap, however, concerns the
separation or absence of eigenvalues, not an approximation error.

= Random graphs, tree spectra, and earlier results

A uniformly random simple $d$-regular graph is chosen with equal
probability from all labeled simple graphs with the prescribed degree.
The degree $d$ is fixed while the vertex count $n$ grows. “With high
probability” means that the probability tends to one. A statement
$X_n arrow.r x$ in probability means that the probability of an error
larger than any fixed positive tolerance tends to zero.

For fixed $d>=3$, the reference spectral interval is

$ [-2 sqrt(d-1),2 sqrt(d-1)]. $

It comes from the infinite $d$-regular tree, the cycle-free graph in
which every vertex has degree $d$. Large random regular graphs look like
this tree near a typical fixed vertex. Most of their eigenvalues fill
the corresponding interval, called the bulk. An isolated eigenvalue
outside it is an outlier. The known eigenvalue $d$ is already outside
the bulk and has to be treated separately.

Friedman's theorem says that the largest absolute nontrivial adjacency
eigenvalue is at most $2 sqrt(d-1)+o(1)$ with high probability. This is
asymptotically optimal, in view of the Alon-Boppana lower bound. Bordenave
gave a later proof and extensions to random lifts [F, B]. A graph is
Ramanujan when its nontrivial eigenvalues satisfy the exact threshold
$abs(lambda)<=2 sqrt(d-1)$.

The distinction between an exact threshold and a threshold plus $o(1)$
is substantial. Huang, McKenzie, and Yau [HMY] determine the fluctuations
at the two edges for fixed-degree random regular graphs. In their
normalization $A/sqrt(d-1)$, edge fluctuations have size
$n^(-2/3+o(1))$ and the limiting edge laws are Tracy-Widom laws. These
are specific probability distributions for rescaled extreme eigenvalues.
Their result gives an asymptotic Ramanujan probability of approximately
69%. The earlier high-probability theorem permits a vanishing excess
above the threshold, so these statements are compatible.

A random lift starts with a fixed base graph. Replace each base vertex
by $N$ copies, its fiber, and replace each base edge by a uniformly
random perfect matching between the two fibers. Each base eigenvector
extends to an assignment constant on each fiber. These are the old
modes. Their orthogonal complement, consisting of assignments with sum
zero in each fiber, carries the new spectrum. A lift inherits one copy
of the base spectrum on the old space, not $N$ copies.

Bordenave and Collins [BC] show that the new spectrum approaches that
of the base graph's universal cover, the infinite tree obtained by
unfolding its walks without retaining cycles. This applies to irregular
bases too. Chen, Garza-Vargas, Tropp, and van Handel [CGTV] give quantitative
strong convergence, controlling fixed matrix polynomials in random
permutations. For fixed positive spectral separation, their bounds have
failure probability $O(1/N)$. Huang and Xu [HX], in an October 2026
preprint, prove local spectral estimates for lifts of fixed connected
simple bases of minimum degree at least three. Away from singular
energies, they resolve scales $(log N)^C/N$ and bound eigenvector
coordinates by $(log N)^C/sqrt(N)$ with high probability. This means the
covered eigenvectors cannot concentrate on only a few vertices.

For a bipartite biregular graph, all left degrees are $d_L$ and all
right degrees are $d_R$. Its adjacency matrix has the form

$ A=mat(0,X;X^T,0), $

where $X$ records edges from left to right. Singular values are the
nonnegative stretching strengths of a matrix, equivalently the square
roots of the eigenvalues of $X^T X$. Nonzero adjacency eigenvalues
are plus and minus the singular values of $X$. The two structural
extremes are $plus.minus sqrt(d_L d_R)$. The tree's positive spectral
band is

$ [abs(sqrt(d_L-1)-sqrt(d_R-1)),sqrt(d_L-1)+sqrt(d_R-1)]. $

Brito, Dumitriu, and Harris [BDH] establish asymptotically sharp spectral
bounds for fixed degrees $d_L,d_R>=3$, with a full-rank consequence when
the degrees differ. Rank counts independent columns, and full rank
means the smaller of the row and column counts. Unequal side sizes still force zero adjacency
eigenvalues. These zeros do not contradict a positive lower edge for
the nonzero band.

= The matching-product results

The main new manuscript is #emph[Centered permutation products] [M].
Its problem is probabilistic. A permutation is a one-to-one matching
between $N$ row labels and $N$ column labels. Write $M_(i j)=1$ if row
$i$ is matched to column $j$, and zero otherwise. Every row and column
contains exactly one 1, and each entry has expectation $1/N$.
Centering replaces the entry by $M_(i j)-1/N$, which has expectation zero.
Expectation, written $bb(E)$, means the average over all possible
permutations.

The entries are dependent. Two distinct diagonal entries illustrate
the effect:

$ bb(E)[(M_(1 1)-1/N)(M_(2 2)-1/N)]=1/(N^2(N-1)). $

Two entries in the same row instead give

$ bb(E)[(M_(1 1)-1/N)(M_(1 2)-1/N)]=-1/N^2. $

The first pattern is smaller by about a factor of $N$. Positions in
the matrix therefore matter, as do repeated factors and whether a
factor is centered.

These products occur in spectral graph questions because a random lift
uses a permutation for each base edge. In a biregular configuration
model, one instead matches half-edges: each vertex supplies as many
edge ends as its degree, and left ends are matched to right ends. The
permutation size is the common half-edge count
$L=n_L d_L=n_R d_R$, so the centering is $1/L$.
Products of matching indicators appear in expected counts of walks.
For example, the trace $"tr"(A^k)$, the sum of its diagonal entries,
equals $sum_i lambda_i^k$ and counts closed walks of length $k$.
This is the link between matching expectations and eigenvalues.

== Refined mixed bounds and exact maxima

A mixed product can contain raw entries, centered entries, powers, and
entries from several independent permutations. Call those independent
permutations colors. A cell consists of a color, row, and column.
Let $a<=N$ be the number of distinct requested cells. A centered
singleton appears once as a centered factor, with no raw copy of that
cell. It is isolated if no other requested cell of its color shares
its row or column. Let $h$ count isolated centered singletons and $b$
count the remaining, conflicting ones. These definitions describe the
requested pattern, before drawing the permutation.

For $2<=a<=sqrt(N)$, the manuscript proves

$ abs(bb(E) P)<=sqrt(e) 2^b N^(-a)
  (sqrt(a-1)/(sqrt(N)-sqrt(a-1)))^h. $

Here $P$ denotes the whole mixed product and $e=exp(1)$. At small
$a/N$, each isolated centered singleton supplies an extra factor of
roughly $sqrt(a/N)$. This refines the $3k/sqrt(N)$ singleton factor in
the earlier estimate, where $k$ counts all factors, including repeats.
The elementary factorial bound contributing $sqrt(e)$ was already known.
The manuscript proves that this prefactor is optimal for its full mixed
class, without claiming first discovery of that factorial inequality.

More precisely, it determines the exact largest possible
$abs(bb(E) P)$ for fixed $N,a,h$ when $b=0$, $b=1$, or $b=2$.
The maximum is over all allowed patterns, powers, and independent colors.
An attained maximum is stronger than an upper bound: an explicit pattern
achieves it, so it cannot be uniformly improved with the same parameters.
For $b=0$, compatible cells in one permutation attain it. For $b=1$, a
raw match forces a conflicting centered entry to be zero. For $b=2$,
two centered cells sharing a row give an attaining pattern. Appendix A
states the exact formulas and a finite recipe for evaluating them.

For larger $b$, stronger upper bounds follow, but exactness is not
claimed. A recorded eight-cell example shows that putting all conflicting
cells in a single row need not maximize the expectation. The general
extremal problem is therefore not settled by the first three cases.
These conclusions correspond to SG-02, SG-06, SG-11, SG-14, and SG-16
in the claim ledger [L].

== Correction to a source argument

The manuscript gives two finite counterexamples to an intermediate
conditioning formula in Bordenave's published equation (62). In one,
conditioning already reveals the cell being tested. In another, exposed
images and preimages remove two matches where the formula counts one.
For a permutation of four elements, it predicts a conditional probability
of $1/3$ where the actual probability is $1/2$. The replacement argument
proves the requested product estimate without that assertion. Proposition
28 and the final spectral theorem are not refuted. This is SG-03, a
correction to an argument rather than a new graph counterexample.

= The diagonal moment results

A second set of results concerns $k$ distinct diagonal centered entries:

$ a_k (N)=bb(E) product_(i=1)^k (M_(i i)-1/N), quad 2<=k<=N. $

The order $k$ is the number of factors. It is allowed to grow with the
permutation size $N$. The first moment is zero and is excluded from the
normalizations below. Collins and Nagatsu [CN] supplied the recurrence
and the leading terms

$ L_(2m)=(2m-1)!! N^(-3m), quad
  L_(2m+1)=(4m/3)(2m+1)!! N^(-3m-2), quad m>=1. $

The double factorial $(2m-1)!!$ means $1 dot 3 dot 5 dots (2m-1)$.
The even and odd leading terms differ. Define $R_k=a_k/L_k$. A ratio
near 1 means the leading term predicts the actual moment accurately
in relative terms. This matters for very small moments: a small absolute
error could still be many times the quantity being estimated.

The symbols $o$ and $O$ describe growing-size limits. The statement
$k=o(N^alpha)$ means $k/N^alpha arrow.r 0$. The statement $X=O(Y)$ means
$abs(X)<=C Y$ for some constant throughout the stated range. An
approximation $X tilde.op Y$ means $X/Y arrow.r 1$. Uniform accuracy means the
largest error over all permitted orders tends to zero, so the statement
covers every order in that range at once.

== The exact cubic threshold

The manuscript proves the necessary and sufficient conditions

$ R_k arrow.r 1 quad arrow.l.r quad k^3/N arrow.r 0, $
$ R_k=O(1) quad arrow.l.r quad k^3/N=O(1). $

The supporting finite bounds include

$ R_k-1>=2k^3/(27N) quad (2<=k<=N), $
$ R_k<=exp(3k^3/N) quad (2k<=N). $

Thus the original leading term is relatively accurate exactly when
$k$ grows more slowly than $N^(1/3)$. At the cube-root scale the error
stops vanishing. Above it the ratio eventually becomes unbounded when
$k^3/N$ diverges. These statements answer the optimal-scale question
posed by Collins and Nagatsu in the specified normalization. The
constant $2/27$ in the lower bound is sharp. These are SG-04 and part
of SG-05. The starting recurrence, SG-01, is prior work.

== The parity-dependent transition

At $k^3/N arrow.r c<infinity$, the limiting ratios are

$ R_k arrow.r cases(
  cosh(2 sqrt(c)/3) & "along even orders",
  sinh(2 sqrt(c)/3)/(2 sqrt(c)/3) & "along odd orders".
) $

Here $cosh(z)=(exp(z)+exp(-z))/2$ and
$sinh(z)=(exp(z)-exp(-z))/2$. The odd quotient is assigned the value 1
at $c=0$. For example, when $k^3/N arrow.r 1$, the limits are about
1.23058 for even orders and 1.07574 for odd orders. The leading term
underestimates both, but by different amounts. SG-05 also supplies a
uniform finite error bound. When $k$ grows with $k^3/N arrow.r 0$,
the ratio $(R_k-1)/(k^3/N)$ tends to $2/9$ for even orders and $2/27$
for odd orders.

The same functions provide a useful approximation beyond the transition.
Put $K=2 floor(k/2)$ and $z=(2/3)sqrt(K^3/N)$, and define

$ H_k=cases(cosh(z) & k" even", sinh(z)/z & k" odd"). $

The odd definition deliberately uses $K=k-1$. SG-07 proves $R_k/H_k
arrow.r 1$ for $k=o(sqrt(N))$, with explicit finite upper and lower
bounds. This is a wider range than the cube-root range of $L_k$ alone.

At $k^2/N arrow.r d>0$, SG-08 determines the next missing factor:

$ R_k/H_k arrow.r exp(d/4). $

Consequently the corrected approximation is
$a_k approx L_k H_k exp(k^2/(4N))$. It is uniformly relatively accurate
on every bounded range $2<=k<=C sqrt(N)$, for fixed $C>0$.

== Further ranges and sharp errors

SG-10 extends the approximation to every sublinear upper range
$2<=k<=b_N$ with $b_N=o(N)$. The formula is

$ a_k tilde.op L_k H_k exp(N G(sqrt(k/N))), $
$ G(t)=sum_(j=4)^infinity (2t^j)/(j(j-2)), quad 0<=t<1. $

The first correction terms in the exponent are

$ N G(sqrt(k/N))=k^2/(4N)+2k^(5/2)/(15N^(3/2))+k^3/(12N^2)+dots. $

The following table states the sharp relative-accuracy ranges for the
successive formulas. Every row concerns the same moment $a_k$.

#figure(table(
  columns: (3.65in, 1fr),
  table.hline(stroke: 0.5pt),
  table.header([Approximation], [Range of relative accuracy]),
  table.hline(stroke: 0.35pt),
  [$L_k$], [$k=o(N^(1/3))$],
  [$L_k H_k$], [$k=o(N^(1/2))$],
  [$L_k H_k exp(k^2/(4N))$], [$k=o(N^(3/5))$],
  [$L_k H_k exp(k^2/(4N)+2k^(5/2)/(15N^(3/2)))$], [$k=o(N^(2/3))$],
  [Full convergent correction $L_k H_k exp(N G(sqrt(k/N)))$], [$k=o(N)$],
  table.hline(stroke: 0.5pt),
), caption: none)

More generally, keeping $G$ through degree $p>=4$ gives the sharp
threshold $k=o(N^((p-1)/(p+1)))$. At the threshold itself a nontrivial
positive factor remains. Thus each extra correction extends the useful
range in a precisely quantified way.

#block(breakable: false)[
SG-09 and SG-12 quantify the error of the shorter formula on the
square-root range. If

$ W_(N,k)=a_k/(L_k H_k exp(k^2/(4N))), $

then, for fixed $C>0$,

$ sup_(2<=k<=C sqrt(N)) abs(W_(N,k)-1)
  =(sqrt(C)/2+2C^(5/2)/15) N^(-1/4)+o(N^(-1/4)). $
]

The paper gives an explicit finite bound as well. The exponent $1/4$
is optimal for this formula and range. Its signed error depends on
parity. At $k/sqrt(N) arrow.r 1$, the scaled errors tend to $-11/30$
for even orders and $19/30$ for odd orders.

SG-13 and SG-15 give a different, fuller formula valid over every
$2<=k<=N$, including the endpoint. Its largest relative error is

$ C_* N^(-1/3)+o(N^(-1/3)), quad C_* approx 0.395496270091. $

The largest errors occur at odd orders near $1.16540187318 N^(1/3)$.
The paper identifies the full limiting parity profile, not only its
maximum. Appendix B states the approximation and profile. The exponents
$1/4$ and $1/3$ describe two different formulas, so they do not conflict.
These estimates concern matching probabilities, rather than rates of
convergence of graph eigenvalues.

= New graph-eigenvalue results in the imported work

The snapshot contains three more concrete graph results. Its review
labels are historical records. They have not received the same later
audits as the permutation manuscript. The following statements use
the corrected accepted reports rather than earlier proposed targets.

== A vertex attached to separated locations

Start with a uniformly random simple $d$-regular graph on $n$ vertices,
where $d>=3$ is fixed. Add one new vertex joined to a fixed set of
$Delta$ labeled host vertices. Here $Delta$ is also fixed. As $n$
grows, those labels lie far apart with high probability.

The bulk edge remains $b_d=2 sqrt(d-1)$. An additional limiting
outlier $lambda_f>b_d$ exists exactly when

$ Delta>2(d-2). $

If this inequality holds, the report [D] gives

$ lambda_f^2=(d^2-(d-2)Delta+
  sqrt((d^2-(d-2)Delta)^2+4(d-1)Delta^2))/2. $

Otherwise define $lambda_f=b_d$. The two largest eigenvalues of the
augmented graph then satisfy, in probability,

$ lambda_1 arrow.r max(d,lambda_f), quad lambda_2 arrow.r min(d,lambda_f). $

The defect can first pull the second eigenvalue out of the bulk and,
when stronger, overtake the host's leading eigenvalue. For a cubic
host, $d=3$, the outcomes are:

#figure(table(
  columns: (1.25in, 1.25in, 1.25in, 1fr),
  align: (left, right, right, right),
  table.hline(stroke: 0.5pt),
  table.header([$Delta$], [Limit of $lambda_f$], [Limit of $lambda_1$], [Limit of $lambda_2$]),
  table.hline(stroke: 0.35pt),
  [2], [2.828427], [3], [2.828427],
  [3], [2.862892], [3], [2.862892],
  [4], [2.946974], [3], [2.946974],
  [5], [3.057527], [3.057527], [3],
  [6], [3.180699], [3.180699], [3],
  table.hline(stroke: 0.5pt),
), caption: none)

#block(breakable: false)[
The report also determines the first finite-size displacement of the
eigenvalue near $d$. Define

$ g_d=(d-1)/(d(d-2)). $
]

#block(breakable: false)[
If $Delta g_d>d$, then

$ n(d-lambda_2) arrow.r Delta^2/(Delta g_d-d). $
]

#block(breakable: false)[
If $Delta g_d<d$, then

$ n(lambda_1-d) arrow.r Delta^2/(d-Delta g_d). $
]

For example, at $d=3,Delta=6$, the first limit is 36, so
$lambda_2=3-36/n+o_P (1/n)$. The subscript $P$ denotes a remainder
small in probability at the displayed scale. For integer $d>=3$ and
integer $Delta$, the equality $Delta g_d=d$ cannot occur, so no
unhandled critical integer case is being suppressed here.

These are adjacency eigenvalue statements for the augmented irregular
graph. Translating them into a normalized-Laplacian or random-walk gap
would require a separate calculation.

The earlier tree calculation [S] concerns a different model: a single
vertex of degree $Delta$ in an infinite tree whose other vertices all
have degree $d$. There the bulk is unchanged and an outlying pair
appears exactly when $Delta>2(d-1)$, at

$ plus.minus Delta/sqrt(Delta+1-d). $

This is not the finite-host threshold $2(d-2)$. Attaching a vertex to
ordinary vertices of a host also increases the degrees of those
attachment vertices, whereas the exceptional-root tree leaves all
other degrees equal to $d$.

== A vertex attached to adjacent locations

Location matters as well as degree. Fix a host vertex $c$ and choose
its least-labeled neighbor $u$. Add a vertex joined to $c$ and $u$.
It has degree two, but the two attachments remain adjacent.

The accepted clustered-family report [A] proves that, at $d=3$,

$ lambda_2 arrow.r 2.8751297941627788 dots, quad lambda_1 arrow.r 3. $

The limiting second eigenvalue is the physical exterior root of
$lambda^3-lambda^2-4lambda-4=0$. It exceeds the bulk edge
$2sqrt(2) approx 2.828427$ by about 0.04670. Two separated attachments
of the same degree do not create this positive outlier. For every
integer $d>=4$, the adjacent-pair second eigenvalue instead tends
to $2sqrt(d-1)$.

The leading correction at the top is

$ n(lambda_1-d) arrow.r (4(d-2))/(d^2-2d-2). $

At $d=3$ this constant is 4, compared with $12/5$ for the separated
pair. Thus even the first finite-size correction detects the pattern
of attachment. The report treats this specific rule for an adjacent
pair. A theorem for every clustered pattern is not established by it.

== An internal gap for lifts of a biregular base

The complete bipartite graph $K_(4,3)$ has four vertices on one side
and three on the other. Their degrees are 3 and 4. The positive band
of its universal-cover spectrum is

$ [sqrt(3)-sqrt(2),sqrt(3)+sqrt(2)]
  approx [0.317837,3.146264]. $

There is also a negative reflected band and a zero contribution from
the unequal side sizes. An $N$-lift has a $4N$ by $3N$ biadjacency
matrix, forcing at least $N$ zero adjacency eigenvalues.

For a fixed compact interval $I$ strictly inside
$(0,sqrt(3)-sqrt(2))$, the report [I] deduces

$ Pr["a new eigenvalue lies in" I]<=C_I/N. $

The constant depends on the chosen interval. A compact interval stays
a positive distance from both endpoints. Consequently this does not
control intervals shrinking toward zero or the band edge. The estimate
is a specialization of quantitative strong convergence [CGTV], not a
new optimal rare-event exponent. A matching lower bound is not proved.
A retained finite lift has a positive eigenvalue near 0.22825, showing
that such an excursion is possible at finite size.

= Other reviewed directions

The initial research synthesis [S] covers eight directions. Several
conclusions are exact translations, examples, or corrections of existing
results. They are useful for interpreting gaps, but should not all be
called new field-wide breakthroughs. The degree-defect and irregular-cover
directions have been discussed above. The remaining conclusions are as
follows.

In the irregular-tree direction, one exact example has continuous
radial bands $plus.minus[sqrt(2)-1,sqrt(2)+1]$ but also an isolated
eigenvalue $sqrt(6)>sqrt(2)+1$. This shows why computing periodic bands
alone can miss the largest eigenvalue when a defect is present. It
does not establish a new general theorem for irregular graph covers.

== Periodic graphs

A periodic graph repeats a fixed pattern across an integer grid.
A finite quotient identifies vertices after a chosen collection of
periods, producing a torus-like graph. Its spectrum is obtained by
sampling the infinite periodic graph's frequency bands at the allowed
frequencies, the Bloch decomposition. A frequency describes an oscillating
pattern across repeated cells. A band records an eigenvalue as that
frequency varies.

Under a positive-definite quadratic curvature assumption at the top
band, the gap is controlled by the smallest nonzero allowed frequency
measured in that quadratic form. For a fixed number $N$ of repeated
cells in $q$ periodic directions, the reviewed range allows gaps of
orders $N^(-2)$ and $N^(-2/q)$ for different quotient shapes. Thus the
number of cells alone does not determine the gap. The result requires
nondegenerate curvature. A claimed extension to singular curvature was
not accepted, and the known periodic-graph exponent is not improved.
Positive-definite curvature here means that the drop from the top band
value is, to leading order, a strictly positive quadratic function of
each small nonzero frequency.

== Hypergraphs

A hyperedge joins a set of vertices rather than just a pair. In an
$r$-uniform, $d$-regular hypergraph, every hyperedge has $r$ vertices
and every vertex belongs to $d$ hyperedges. Let $X$ be the vertex by
hyperedge incidence matrix. For the adjacency that counts shared
hyperedges between distinct vertices,

$ A_H=X X^T-d I. $

Its top eigenvalue is $d(r-1)$, and its smallest eigenvalue is at least
$-d$. The multiplicity of $-d$ is exactly
$"number of vertices"-"rank"(X)$. If there are fewer hyperedges than
vertices, some such eigenvalues are forced. This explains both the
correct top gap and a lower spectral plateau. Merely choosing
three-vertex or four-vertex hyperedges does not justify replacing the
second eigenvalue by the third or fourth.

== Directed graphs

Directed edges have arrows, so adjacency need not be symmetric.
Eigenvalues may be complex, and their absolute values can differ from
singular values. A singular value is the square root of an eigenvalue
of $A^T A$ and measures one-step stretching. A real matrix is normal
when $A A^T=A^T A$. For normal matrices singular values equal the
absolute eigenvalues, with multiplicity. Without normality, a singular
value estimate cannot simply be relabeled an eigenvalue estimate.

The reviewed directed results separate these two quantities. They
include an asymptotic lower bound $2sqrt(d-1)-o(1)$ for the second
singular value of large $d$-in, $d$-out regular digraphs. The corresponding
absolute-eigenvalue conclusion needs normality and removal of peripheral
modes. If a strongly connected digraph has period $m$, defined as the
greatest common divisor of its directed cycle lengths, it has $m$
eigenvalues of modulus $d$. The first informative index is then $m+1$.
This explains when higher gap indices really do have a structural basis.

A separate November 2026 preprint of Bordenave and Zhu [BZ] proves a
high-probability lower bound on the second transition eigenvalue in
modulus for a directed configuration model, matching the earlier upper
bound under its degree hypotheses. That is an external result, not a
new theorem produced by this packet.

== Cayley graphs and multiplicities

A Cayley graph uses a finite group as its vertices and joins $x$ to
$x s$ for specified generators $s$. A group is a set with an associative
multiplication, an identity, and inverses. In the binary group
$bb(F)_2^q$, vertices are bit strings and addition is coordinatewise
exclusive-or. For a generating set $S$ of size $d$, its eigenvalues
are

$ lambda_u=sum_(s in S)(-1)^(u dot s)=d-2 w_u. $

The dot product is computed modulo two and $w_u$ counts the generators
with $u dot s=1$. The strings $(u dot s)_(s in S)$ form a binary linear
code, a vector space of bit strings. Its smallest nonzero weight gives
the second eigenvalue. Connectivity requires $q<=d$, so fixed degree
bounds this group's size by $2^d$. There is no unbounded connected
fixed-degree family of this particular kind.

For noncommutative finite groups, the analogous decomposition uses
matrix blocks instead of scalar characters. The packet records exact
small-group classifications and examples locating obstructing blocks.
It does not establish a new general asymptotic bound for such graphs.

The multiplicity direction also checks a standard bound for the Seidel
matrix $S=J-I-2A$, where $J$ is all ones. If an eigenvalue $theta$ has
multiplicity $m$, then

$ m<=n(n-1)/(n-1+theta^2). $

Equality forces only two distinct Seidel eigenvalues. Exact Cartesian
product examples show repeated second adjacency eigenvalues and many
large eigenvalues. The first two spectral moments alone do not prove
a general small-multiplicity theorem. This is a limitation on what a
proposed argument can conclude, rather than a new random-graph gap law.

= What is new, and what remains unresolved

The exact mixed maxima for zero, one, and two conflicting centered
singletons are the main finite extremal contribution candidates. The
diagonal results determine sharp validity ranges, transition laws, and
errors in a specific probabilistic normalization. The source audit finds
substantial overlap with existing permanent inequalities and classical
Laguerre, derangement, and Whittaker formulas. The recurrence and leading
terms are explicitly credited to Collins and Nagatsu. Historical
firstness of the complete diagonal formulas remains unverified.

The finite-defect and adjacent-attachment results turn earlier conditional
predictions in the archive into graph-eigenvalue theorems for specified
models. Their internal acceptance records are not comprehensive novelty
audits. The $K_(4,3)$ internal-gap bound is an application of an existing
quantitative theorem. Across these results, model, operator, structural
subspace, and limiting regime must be retained when interpreting a gap.

No end-to-end formal verification is claimed for the spectral-gap packet.
The main manuscript has separate mathematical review records for SG-01
through SG-16. Its latest frozen revision is 10, and the recorded final
assembled delta review and release replay are pending. The imported
batch-060 archive also retains two reports awaiting verdict. Pending
reports have not been promoted to results here. Internal proof review,
finite numerical checks, and an external priority assessment are distinct
kinds of evidence.

Open extensions include the exact mixed maximum for more than two
conflicting singletons, an improved final graph theorem using the refined
mixed bounds, a sharp lower probability for internal-gap excursions,
general clustered attachment patterns, growing defect sets, and bulk-edge
fluctuations for the defect models. The block-Krylov spectral-gap result
in the separate matrix-multiplication project concerns convergence of a
matrix algorithm. It is not a graph expansion theorem and is outside
this packet's graph results.

#heading(numbering: none)[Appendix A. The exact finite mixed formulas]

This appendix gives the formulas behind the three attained maxima.
For an integer $s>=0$, the falling factorial is
$(N)_s=N(N-1)dots(N-s+1)$, with $(N)_0=1$.
Define a polynomial $P_h (N,r)$ by splitting $h$ labeled objects into
disjoint nonempty groups in every possible way. A group of size $j$
receives weight $((j-1)N+r)(j-1)!$. Multiply the weights within each
partition and add over partitions. The empty partition contributes 1.
For example,

$ P_0=1, quad P_1=r, quad P_2=r^2+r+N. $

With the definitions of $a,h,b$ in Section 4, write

$ E_0=(N^(-h) P_h (N,a-h))/(N)_a, $
$ E_1=(N^(-h-1) P_h (N,a-h-1))/(N)_(a-1), $
$ E_2=(2N^(-h-1)P_h (N,a-h-1))/(N)_(a-1)
       -(N^(-h-2)P_h (N,a-h-2))/(N)_(a-2). $

For $2<=a<=N$, the exact maxima at $b=0,1,2$ are respectively
$E_0,E_1,E_2$. For the latter two cases require $0<=h<=a-2$.
The general bounds are $2^b E_0$, $2^(b-1)E_1$ when $b>=1$, and
$2^(b-2)E_2$ when $b>=2$. Exactness beyond $b=2$ is not asserted.

For example, at $a=2,h=2,b=0$, the maximum is
$N/(N)_2 dot N^(-2)=1/(N^2(N-1))$. At $a=2,h=0,b=2$, it is
$2/(N(N)_1)-1/N^2=1/N^2$. These recover the two elementary centered
products above. Arbitrarily high integer powers and arbitrarily many
independent colors are allowed within the distinct-cell restriction
$a<=N$.

#heading(numbering: none)[Appendix B. The full-range diagonal approximation]

#block(breakable: false)[
Keep $R_k,L_k,H_k,K$ from Section 5. Put

$ eta=k-K in {0,1}, quad x=sqrt(K/N), quad D_k=N^k/(N)_k, $
$ q(x)=x+(x^2-1)log(1+x)-x^2/2-2x^3/3. $
]

Then define

$ cal(A)_(N,k)=D_k H_k exp(N q(x))(1+x)^(eta-1/2). $

The full-range statement is

$ sup_(2<=k<=N) abs(a_k/(L_k cal(A)_(N,k))-1)
    =C_* N^(-1/3)+o(N^(-1/3)). $

#block(breakable: false)[
Every factor is finite and positive, including at $k=N$. Keeping the
falling factorial exact is important near that endpoint. The complete
signed error profile can be written using

$ ell(c)=(2/3)c^(3/2), $
$ p_0 (t)=t tanh(t), quad p_1 (t)=t coth(t)-1, $
$ Phi_eta (c)=(3(2eta-1))/(4c)(p_eta (ell(c))-ell(c)). $
]

The functions are $tanh(t)=sinh(t)/cosh(t)$ and
$coth(t)=cosh(t)/sinh(t)$ for $t>0$.

The profile extends continuously to zero with value zero. Uniformly over
all $2<=k<=N$, the scaled relative error $N^(1/3)(R_k/cal(A)_(N,k)-1)$
approaches $Phi_(k mod 2)(k/N^(1/3))$. Its largest absolute value is
$C_* approx 0.395496270091$, attained on the odd branch near
$c approx 1.16540187318$.

#heading(numbering: none)[Sources]

#set text(size: 9pt)
#set par(justify: false, leading: 0.35em, spacing: 0.45em)

[M] #link("manuscript-round-01/output/pdf/centered-permutation-products.pdf")[Centered permutation products: sharp envelopes and uniform asymptotics.]
Latest reading manuscript, frozen revision 10, 41 pages. Local working paper, November 2026.

[L] #link("CLAIM_LEDGER.md")[Authoritative claim ledger],
#link("CONTRIBUTION.md")[contribution statement], and
#link("extension-round-02/PRIORITY_SYNTHESIS.md")[priority assessment].
These distinguish known inputs, new refinements, and review scope.

[D] #link("snapshot/results/050-finite-defect.md")[Finite-defect resolvent and limiting eigenvalues].
[A] #link("snapshot/results/spectral-research/batch-060/review-adjacent-accepted.md")[Accepted adjacent-attachment family].
[I] #link("snapshot/results/040-internal-gap-theorem.md")[Internal-gap assessment].
[S] #link("snapshot/results/030-spectral-research-synthesis.md")[Synthesis of eight spectral research directions].
Later result records take precedence over its older open-problem list.

[F] J. Friedman. #link("https://arxiv.org/abs/cs/0405020")[A proof of Alon's second eigenvalue conjecture and related problems]. Memoirs of the AMS, 2008.

[B] C. Bordenave. #link("https://arxiv.org/abs/1502.04482")[A new proof of Friedman's second eigenvalue theorem and its extension to random lifts]. Annales scientifiques de l'École normale supérieure, 2020.

[BDH] G. Brito, I. Dumitriu, K. D. Harris. #link("https://arxiv.org/abs/1804.07808")[Spectral gap in random bipartite biregular graphs and applications]. Combinatorics, Probability and Computing, 2022.

[BC] C. Bordenave, B. Collins. #link("https://arxiv.org/abs/1801.00876")[Eigenvalues of random lifts and polynomials of random permutation matrices]. Annals of Mathematics, 2019.

[CGTV] C.-F. Chen, J. Garza-Vargas, J. A. Tropp, R. van Handel. #link("https://arxiv.org/html/2405.16026v3")[A new approach to strong convergence]. Annals of Mathematics, 2026. Theorem 3.9 is the quantitative input for the internal-gap specialization.

[CN] B. Collins, M. Nagatsu. #link("https://arxiv.org/abs/2503.18453")[Weingarten calculus for centered random permutation matrices]. Algebraic Combinatorics 9, 2026, 465 to 479. The local audit also checked the published version.

[HMY] J. Huang, T. McKenzie, H.-T. Yau. #link("https://arxiv.org/abs/2412.20263")[Ramanujan Property and Edge Universality of Random Regular Graphs]. Preprint, revised February 2025.

[HX] J. Huang, R. Xu. #link("https://arxiv.org/abs/2610.37463")[Local Law and Eigenvector Delocalization for Random Lifts]. Preprint, October 2026.

[BZ] C. Bordenave, Y. Zhu. #link("https://arxiv.org/abs/2611.07104")[A second eigenvalue lower bound for the directed configuration model]. Preprint, November 2026.

Further background: D. Spielman, #link("https://www.cs.yale.edu/homes/spielman/eigs/lect1.pdf")[Spectral Graph Theory and its Applications, Lecture 1]. External sources checked on 14 November 2026.
