# Derivation notes

**Method:** Paper statements are labeled explicitly. Algebra and case analysis reconstructed here are **Derived**. Interpretive readings are separated where needed. Numerical spot checks are flagged but were not run.

Use $a=d_1-1$, $b=d_2-1$, $\rho=\sqrt{ab}$, and $\tau=(ab)^{1/4}$ as defined in the notation file.

## D1. Block-matrix spectrum and the two spectral edges

**1. Target:** Derive the adjacency spectrum in terms of singular values of $X$, identify the Perron pair, and clarify what $\eta$ means.

**2. Where it appears:** Equation 1 and surrounding discussion, Section 1.1, page 2.

**3. Inputs:** The symmetric block matrix

$$A=\begin{pmatrix}0&X\\X^*&0\end{pmatrix},$$

where $X\in\mathbb R^{n\times m}$ has row sums $d_1$ and column sums $d_2$.

**4. Derivation:** If $(u,v)$ is an eigenvector with value $\xi$, then

$$Xv=\xi u,\qquad X^*u=\xi v.$$

If $\xi\neq0$, both vectors are nonzero. Applying $X^*$ to the first equation and $X$ to the second gives

$$X^*Xv=\xi^2v,\qquad XX^*u=\xi^2u.$$

The Birman-type sign symmetry is even more direct:

$$\begin{pmatrix}I&0\\0&-I\end{pmatrix}
A
\begin{pmatrix}I&0\\0&-I\end{pmatrix}=-A.$$

Thus $\xi$ and $-\xi$ occur together. For $\xi=0$, the equations reduce to $Xv=0$ and $X^*u=0$ independently. If $r=\operatorname{rank}X$, these nullspace dimensions are $m-r$ and $n-r$ respectively.

The all-ones equations are

$$X\mathbf1_m=d_1\mathbf1_n,\qquad X^*\mathbf1_n=d_2\mathbf1_m.$$

Take $u=\sqrt{d_2}\mathbf1_n$ and $v=\sqrt{d_1}\mathbf1_m$. Then $Xv=d_1\sqrt{d_1}\mathbf1_n$ while $\xi u=\xi\sqrt{d_2}\mathbf1_n$, so $\xi=\sqrt{d_1d_2}$. The second equation agrees. Perron-Frobenius identifies this positive value as the leading magnitude. Its negative partner also occurs.

The second nonnegative singular value is therefore both $\lambda_2(A)$ and $-\lambda_{n+m-1}(A)$ after the negative leading partner is accounted for.

**5. Dimensional or type check:** $u\in\mathbb R^n$, $v\in\mathbb R^m$. $XX^*$ acts on $\mathbb R^n$, while $X^*X$ acts on $\mathbb R^m$.

**6. Hidden assumptions:** Simplicity gives $X\in\{0,1\}^{n\times m}$, but the algebra also works for nonnegative weighted $X$ with the same row and column sums. Connectivity is needed for a one-dimensional Perron eigenspace.

**7. Intuition:** Positive and negative eigenvalues are two views of the same singular values. A rectangular $X$ has unavoidable zero eigenvalues in $A$, and the interesting second spectral edge is the second singular value.

**8. Failure modes:** Saying “the second largest in absolute value” without excluding the negative Perron partner gives $-\sqrt{d_1d_2}$ rather than $\eta$. The paper's $\lambda_2(A)$ is signed second largest, not second largest absolute value over all eigenvalues without qualification.

**9. Numeric check (optional):** Construct a small rectangular regular $X$ and compare eigenvalues of $A$ with singular values of $X$. Not run.

**10. Remember this:** The whole problem can be read in $X^*X$ or $XX^*$. Nonzero adjacency eigenvalues carry no independent sign information after squaring.

---

## D2. Ihara-Bass transfer, bulk circle, lower edge, and full row rank

**1. Target:** Derive Equations 6 to 8 and use Theorem 3 to obtain every part of Theorem 4.

**2. Where it appears:** Theorem 1 through Theorem 4, pages 6 to 9, especially Equations 4 to 8.

**3. Inputs:** Ihara-Bass, $D=\operatorname{diag}(aI_n,bI_m)$, $A$ in block form, a non-backtracking eigenvalue $\lambda\notin\{\pm1\}$, and $r=\operatorname{rank}X$. Use $y=\xi^2$ for an adjacency eigenvalue $\xi$ and $x=\lambda^2$.

**4. Derivation:**

### D2.1 The quadratic relation

The determinant singularity equation $(D-\lambda A+\lambda^2I)v=0$ splits into

$$Xv_2=\frac{a+\lambda^2}{\lambda}v_1,
\qquad X^*v_1=\frac{b+\lambda^2}{\lambda}v_2.$$

This is Equations 4 and 5. For the nonzero singular-value branch, multiply the appropriate compositions to obtain

$$XX^*v_1=\frac{(a+\lambda^2)(b+\lambda^2)}{\lambda^2}v_1,
\qquad X^*Xv_2=\frac{(a+\lambda^2)(b+\lambda^2)}{\lambda^2}v_2.$$

Thus

$$y=\xi^2=\lambda^2+\frac{ab}{\lambda^2}+a+b
=x+\frac{ab}{x}+a+b.\tag{Derived form of Equations 6 and 7}$$

Rearranging gives

$$x^2+ab=(y-a-b)x,$$

which is Equation 8, and

$$x^2-(y-a-b)x+ab=0.$$

### D2.2 Zero adjacency eigenvalues and exact imaginary roots

If $u\in\ker X$, take $(v_1,v_2)=(0,u)$. Equations 4 and 5 become identities precisely when

$$b+\lambda^2=0,$$

so $\lambda=\pm i\sqrt b$. There are $m-r$ independent choices on each sign branch. Similarly, $w\in\ker X^*$ with $(v_1,v_2)=(w,0)$ gives $\lambda=\pm i\sqrt a$, each with multiplicity $n-r$. This derives the corrected Lemma 2 classification recorded in `05-main-results.md`.

There is no $\lambda=0$ eigenvalue because at $\lambda=0$ the Ihara-Bass matrix reduces to $D$, whose diagonal entries are nonzero under the degree assumptions.

### D2.3 Why bulk means complex conjugate roots on a circle

Consider the scalar function

$$y=f(x)=x+\frac{ab}{x}+a+b.$$

For $y\in\mathbb R$, its imaginary part imposes a useful constraint. Writing $x=u+iv$, compute

$$\operatorname{Im}\left(x+\frac{ab}{x}\right)
=v-\frac{ab\,v}{u^2+v^2}
=v\left(1-\frac{ab}{|x|^2}\right).$$

If $v\neq0$, reality of $y$ forces $|x|^2=ab$. The two roots have product $ab$, so in this case they are conjugate square roots $x,\bar x$ of one point on $|x|=\sqrt{ab}$. Consequently,

$$|\lambda|=\sqrt{|x|}=(ab)^{1/4}=\tau.$$

The quadratic discriminant clarifies when this occurs:

$$\Delta(y)=(y-a-b)^2-4ab
=\left(y-(\sqrt a+\sqrt b)^2\right)
 \left(y-(\sqrt a-\sqrt b)^2\right).$$

For

$$(\sqrt a-\sqrt b)^2<y<(\sqrt a+\sqrt b)^2,$$

we have $\Delta<0$. This is the bulk interval found above.

### D2.4 Above the upper bulk edge gives real outer roots

If $y\geq(\sqrt a+\sqrt b)^2$, then $\Delta\geq0$. The coefficients force two positive values of $x$, with product $ab$. On a positive real branch,

$$f'(x)=1-\frac{ab}{x^2}.$$

At $x=\sqrt{ab}$,

$$f(\sqrt{ab})=2\sqrt{ab}+a+b=(\sqrt a+\sqrt b)^2.$$

For $x>\sqrt{ab}$, $f'>0$ and therefore $f(x)$ is above the upper bulk endpoint. Hence any larger $y$ has an outer root $x_+>\sqrt{ab}$. Its positive $\lambda=\sqrt{x_+}$ satisfies $\lambda>\tau$.

The contrapositive is the transfer needed for Theorem 4(i): if no non-leading $B$ eigenvalue exceeds $\tau+\epsilon_n$, no adjacency singular value can exceed a continuously determined upper-bulk neighborhood. Taking roots converts the additive non-backtracking error into an adjacency $\epsilon_n'\to0$ because $f$ and the outer root depend continuously on the spectral variable around the finite threshold.

### D2.5 Below the lower edge gives purely imaginary roots

Suppose $0<y\leq(\sqrt a-\sqrt b)^2$. The discriminant is nonnegative, while

$$y-a-b<0.$$

The two roots have negative sum and positive product, so both are real and negative. Write $x=-q$, $q>0$. Then

$$y=a+b-q-\frac{ab}{q}.$$

Set $u_0=\sqrt a-\sqrt b$. By $q+ab/q\geq2\sqrt{ab}$,

$$u_0^2=a+b-2\sqrt{ab}\geq y=a+b-q-\frac{ab}{q},$$

so

$$q+\frac{ab}{q}\geq2\sqrt{ab}.$$

At the lower edge equality gives $q=\sqrt{ab}$. As $y$ increases from 0 to $u_0^2$, one negative root moves from $-a$ to $-\sqrt{ab}$ and the other from $-b$ to $-\sqrt{ab}$. Explicitly,

$$\frac{d}{dq}\left(a+b-q-\frac{ab}{q}\right)
=-1+\frac{ab}{q^2}.$$

This is positive for $q<\sqrt{ab}$ and negative for $q>\sqrt{ab}$, proving the two monotonic branches. In all cases $\lambda=\pm i\sqrt q$, so the non-backtracking roots are purely imaginary. The root nearest the circle crosses $\tau$ as $y$ drops below the lower edge.

The same exclusion argument as above gives Theorem 4(ii). A singular value below the lower bulk edge would create an outer imaginary non-backtracking root beyond $\tau+\epsilon_n$ after allowing a small continuous margin.

### D2.6 Full row rank

If $r<n$, then $\dim\ker X^*=n-r>0$. D2.2 gives actual eigenvalues $\pm i\sqrt a$ of $B$. Their magnitude is

$$\sqrt a.$$

When $a>b$,

$$\sqrt a>(ab)^{1/4}=\tau.$$

Once $\epsilon_n<\sqrt a-\tau$, Theorem 3's high-probability event excludes these eigenvalues. Therefore $r=n$ with high probability. This is the entire rank argument. It does not use the structural nullspace of dimension $m-r$ on the other side.

**5. Dimensional or type check:** $x$ and $y$ are squared spectral variables. The quadratic lives over $\mathbb C$ for $x$, but $y\geq0$ because $\xi$ is real. In the bulk, $|\lambda|=|x|^{1/2}$, not $|x|$ or $|x|^2$.

**6. Hidden assumptions:** $a,b>0$. Continuity is used only in compact neighborhoods of finite spectral thresholds, so no uniform global continuity estimate is required. The rank argument needs the strict gap $\sqrt a-\tau>0$.

**7. Intuition:** Squaring turns the four $B$ roots of an adjacency pair into the two $x$ roots. In the bulk they are conjugates on a circle. Outside it they become real positive or real negative $x$, producing respectively real or imaginary $\lambda$ outliers.

**8. Failure modes:**

- Copying the printed multiplicities in Lemma 2 breaks the count and can obscure the rank proof.
- Treating $x=\lambda$ instead of $x=\lambda^2$ changes every radius.
- Applying the rank argument to $d_1=d_2$ fails because $\sqrt a=\tau$, leaving no strict exclusion margin.
- Confusing $\sqrt a$ with the printed $a^{1/4}$ is easy. If $\lambda=\pm i\sqrt a$, then $|\lambda|=\sqrt a$ because $\lambda^2=-a$. The paper's $a^{1/4}$ remarks concern a different bound on $|x|$ in one branch.

**9. Numeric check (optional):** Choose $a=6,b=2$ and evaluate outer roots for $y$ just inside, above, and below the bulk interval. Not run.

**10. Remember this:** Theorem 3 plus the scalar map $f(x)$ yields all three adjacency conclusions. Full row rank is simply exclusion of $\pm i\sqrt a$.

---

## D3. The matching factorization and tangle-free decomposition

**1. Target:** Explain $B=MN$, derive the centering matrices $S,S'$, and give the intended algebra behind Equations 12 to 17.

**2. Where it appears:** Equation 9, page 10, and Section 5.2, pages 13 to 15.

**3. Inputs:** Half-edge matching matrix $M$, deterministic half-edge selector $N$, block-average matrix $S$, and path families $\Gamma,F,T$.

**4. Derivation:**

### D3.1 Why $B=MN$

A nonzero product $M_{eg}N_{gf}$ does two things. First, $M_{eg}$ matches the endpoint of one oriented edge to $g$. Second, $N_{gf}$ chooses another half-edge $f$ at the same vertex, with a different label. Excluding the identical label prevents immediate backtracking. Summing over $g$ gives exactly the non-backtracking transition $B_{ef}$.

### D3.2 Remove the row-average matrix

The paper defines

$$S=\frac1{|E|}
\begin{pmatrix}0&(d_2-1)JJ^*\\(d_1-1)JJ^*&0\end{pmatrix},$$

where both $J$ blocks are all-ones vectors. The coefficient arises because $N$ has respectively $d_2-1$ and $d_1-1$ eligible choices per row in the two block directions.

Choose

$$S'=\frac1{|E|}\begin{pmatrix}0&JJ^*\\JJ^*&0\end{pmatrix}.$$

Then $S'N=S$, so

$$\bar B=B-S=MN-S'N=(M-S')N=\bar MN.$$

This is the algebraic reason that an ordinary expectation-centering of the permutation matrix $M$ can be used for the almost-centered $\bar B$.

The range of $S$ consists of vectors constant separately on the two blocks, equivalently $\operatorname{span}\{\mathbf1_\alpha,\mathbf1_{-\alpha}\}$. In contrast, $\ker S$ is the space of vectors whose two block means vanish. These are different subspaces. This distinction corrects the confused sentence below Equation 13.

### D3.3 Path expansion and centering

Since $N=1$ along any non-backtracking half-edge path in $\Gamma^\ell_{ef}$, Equation 12 reads

$$(B^\ell)_{ef}=\sum_{\gamma\in\Gamma^\ell_{ef}}
\prod_{t=1}^{\ell}M_{e_{2t-1}e_{2t}}.$$

Equation 13 replaces $M$ by $\bar M$ after substituting $\bar B=(M-S')N$.

### D3.4 Telescoping identity with correct indices

For scalars $x_s,y_s$, induction on $\ell$ proves

$$\prod_{s=1}^{\ell}x_s
=\prod_{s=1}^{\ell}y_s+
\sum_{j=1}^{\ell}
\left(\prod_{s=1}^{j-1}y_s\right)(x_j-y_j)
\left(\prod_{t=j+1}^{\ell}x_t\right).$$

The base case $\ell=1$ is $x_1=y_1+(x_1-y_1)$. Appending a new factor and applying induction yields the next case.

Substitute $x_s=B_{e_{2s-1}e_{2s+1}}$ and $y_s=\bar B_{e_{2s-1}e_{2s+1}}$. Then $x_j-y_j=S_{e_{2j-1}e_{2j+1}}$. This exactly gives Equation 14.

At matrix level, the prefix contains $j-1$ factors of $\bar B$, not $j$. The intended central product in the decomposition is

$$\bar B^{(j-1)}S B^{(\ell-j)},$$

with suitable tangle-free parentheses. Printed Equation 16 writes $\bar B^{(j)}S B^{(\ell-j)}$, an off-by-one mismatch with Equation 14.

On $x\in\ker T$, the block means vanish and $B^{(\ell-j)}x$ preserves this property. Multiplication by $S$ kills the vector, so the central telescoping terms vanish. Equivalently, $S$ composed with a mean-preserving matrix has zero action on $\ker S$. The statement in the paper that $B^{(\ell-j)}x$ lies in $\ker S$ “since it is just the space spanned by the leading eigenvectors” conflates the mean-zero kernel with the leading-eigenvector range.

After restricting every path to tangle-free pieces, the unmatched terms form remainder matrices $R^{\ell,j}$, yielding the intended norm bound

$$\|B^{(\ell)}x\|\leq\|\bar B^{(\ell)}\|+
\sum_{j=1}^{\ell}\|R^{\ell,j}\|.$$

The redundant inner $\sum_{j=1}^{\ell}$ in printed Equation 15, where $j$ is already a fixed parameter of $T^{\ell,j}_{ef}$, should be removed.

**5. Dimensional or type check:** $M,N,S,S',\bar M$ all act on the same $2|E|$-dimensional half-edge space. The all-ones blocks have rectangular dimensions appropriate to the bipartition. The kernel $\ker S$ has codimension two, while $\operatorname{range}S$ has dimension two.

**6. Hidden assumptions:** Half-edge labels remain distinct. On the conditioned simple graph, no two wire matchings join the same vertex pair, but the configuration model itself permits parallel edges. Mean-zero preservation must be checked for the tangle-free restricted matrices as well as for $B^\ell$.

**7. Intuition:** Matching indicators are random only through $\pi$. Subtracting the universal permutation mean is what makes rare centered circuit patterns cancel, while $N$ merely enforces non-backtracking geometry.

**8. Failure modes:** The printed index and subspace errors cannot be used literally. Also, a composition of individually tangle-free paths need not be tangle-free, which is precisely why the $R^{\ell,j}$ terms cannot just be discarded.

**9. Numeric check (optional):** Verify the telescoping identity for random scalar sequences of lengths 1 to 8. Not run.

**10. Remember this:** The intended identity is centered main term plus zero-on-$\ker S$ telescoping terms minus tangled remainders. All later combinatorics exists to control those two nonzero pieces.

---

## D4. From spectral norm to circuit moments and three regimes

**1. Target:** Derive Equations 11, 24, and 25 and explain the inequalities $\mathscr E\leq k\ell$ and $\mathscr E_1'\geq2(\mathscr V-k\ell)$.

**2. Where it appears:** Sections 5.1 and 5.8, pages 13 and 20 to 22.

**3. Inputs:** Any real matrix $C=\bar B^{(\ell)}$, its singular values, and trace expansion of $(CC^*)^k$.

**4. Derivation:** Let $s_1\geq\cdots\geq s_r\geq0$ be the singular values of $C$. Then

$$\|C\|=s_1,\qquad CC^*\text{ has eigenvalues }s_i^2.$$

Consequently,

$$\|C\|^{2k}=s_1^{2k}\leq\sum_i s_i^{2k}
=\operatorname{Tr}((CC^*)^k).$$

Taking expectations gives

$$\mathbb E\|C\|^{2k}\leq
\mathbb E\operatorname{Tr}((CC^*)^k).$$

No positive definiteness of $C$ is required. The trace uses $CC^*$, which handles arbitrary real $C$.

Expand the $2k$ matrix factors. Their product is closed by the trace, so each nonzero entry product corresponds to a circuit of $2k$ segments. Matrix and adjoint legs alternate traverse direction, which Figure 4 depicts. The fact that all segments are tangle-free does not imply that the union has at most one cycle.

Now split circuits:

$$\mathcal C_1=\{\text{each edge appears at least twice}\},$$

$$\mathcal C_2=\{\text{some singleton edge and }\mathscr V\leq k\ell+1\},$$

$$\mathcal C_3=\{\text{some singleton edge and }\mathscr V>k\ell+1\}.$$

For $\mathcal C_1$, there are $2k\ell$ edge traversals up to the shared-leg convention and each distinct edge uses at least two, hence

$$\mathscr E\leq k\ell.$$

Connectedness gives $\mathscr V-1\leq\mathscr E$, so $\mathscr V\leq k\ell+1$.

For $\mathcal C_2$, existence of a singleton edge prevents a tree support because every connected circuit union has cycle in the trace construction at these regimes as used by the authors. Thus $\mathscr E\geq\mathscr V$ and $\chi\geq1$.

For $\mathcal C_3$, let $\mathscr E_1'$ count all multiplicity-one edges. Since all other edges appear at least twice,

$$2k\ell\geq2(\mathscr E-\mathscr E_1')+\mathscr E_1'
=2\mathscr E-\mathscr E_1'.$$

With $\mathscr E\geq\mathscr V=k\ell+t$,

$$\mathscr E_1'\geq2\mathscr E-2k\ell\geq2t.$$

At most $b_\mathcal C\leq4(k+\chi)$ of these are inconsistent, so the consistent singleton count obeys

$$\mathscr E_1=\mathscr E_1'-b_\mathcal C
\geq(2t-4(k+\chi))_+.$$

This forces extra powers of $k\ell/\sqrt{|E|}$ through Lemma 7 and is why large-vertex circuits do not beat the main $\alpha^{2k\ell}$ scale.

**5. Dimensional or type check:** The left side of the trace comparison is a scalar operator norm raised to $2k$. The right is a scalar Schatten $2k$-moment. The trace has real nonnegative summands before centering is expanded into signed entries.

**6. Hidden assumptions:** The circuit count must respect shared endpoints of legs. Counting $\ell+1$ per leg without subtracting duplicated joins would add $2k$ traversals, while Lemma 9's stated circuit length uses $2k\ell$.

**7. Intuition:** Dominant paths spend their traversals economically on repeated edges. If many edges or vertices are visited, many first appearances must be paid for with centering penalties.

**8. Failure modes:** Treating the trace as ordinary $\operatorname{Tr}C^{2k}$ would miss non-normality and alternating transposes. Ignoring the difference between distinct edges and traversals destroys the key regimes.

**9. Numeric check (optional):** Compare both sides of the singular-value trace inequality on small random matrices. Not run.

**10. Remember this:** $\mathcal C_1$ supplies the leading tree-like term, $\mathcal C_2$ pays one cycle factor, and $\mathcal C_3$ pays many singleton factors.

---

## D5. Circuit encoding and the degree-count algebra

**1. Target:** Explain the exponents in Lemmas 9 to 11 and reproduce the main cancellation that leads toward Equation 26, while isolating the Corollary 12 audit issue.

**2. Where it appears:** Sections 5.4 to 5.8, pages 16 to 21, supported by Figure 5.

**3. Inputs:** Ordered discovery vertices, first-discovery spanning tree $\mathcal T_\gamma$, triples $(p_i,q_i,r_i)$, cycle excess $\chi=\mathscr E-\mathscr V+1$, and the $(d_1,d_2)$ regularity equations.

**4. Derivation:**

### D5.1 Triple count

A type-1 path is determined by its endpoint because a tree has a unique route between two vertices. A type-2 path discovers new vertices, so its length suffices under the fixed discovery order. A type-3 path is one non-tree edge to an old vertex, hence its final vertex suffices. This gives at most

$$(\mathscr V+1)^2(\ell+1)$$

choices per triple.

By Lemma 8, only the final triple can avoid a non-tree edge. The circuit supplies at most $\chi$ such edges, so one leg has at most $\chi+1$ relevant triples. The one-cycle modification additionally places two delimiters, with at most $\ell$ choices each, giving a factor $\ell^2$. Combining tree and cycle cases generously multiplies by 2. Across $2k$ segments, this explains the factor $(2\ell)^{4k}((\mathscr V+1)^2(\ell+1))^{2k(\chi+1)}$ in Lemma 9 after further generous bounding.

Splitting each remainder path into three tangle-free subpaths produces at most

$$\left[(2\ell)((\mathscr V+1)^2(\ell+1))^{\chi+1}\right]^3$$

per segment, hence the larger exponents in Lemma 10.

### D5.2 Ordered vertices and half-edge labels

Choosing ordered discovery vertices on the two sides costs at most

$$m^{\mathscr R}n^{\mathscr V-\mathscr R}.$$

For one left vertex $v$ of induced degree $g_v$, choosing its labeled incident half-edges costs at most $d_1(d_1-1)^{g_v-1}$. Summing left induced degrees gives $\mathscr E$. The analogous right calculation yields exactly Lemma 11.

### D5.3 Cancel actual graph sizes against matching probabilities

Write $L=\mathscr V-\mathscr R$. The factors $|E|^{-\mathscr V}$ that emerge when the vertex and half-edge factors are reorganized cancel via

$$n^Ld_1^L=\left(\frac{|E|}{d_1}\right)^Ld_1^L=|E|^L,$$

$$m^{\mathscr R}d_2^{\mathscr R}
=\left(\frac{|E|}{d_2}\right)^{\mathscr R}d_2^{\mathscr R}
=|E|^{\mathscr R}.$$

Thus

$$\frac{n^Lm^{\mathscr R}d_1^Ld_2^{\mathscr R}}{|E|^{\mathscr V}}=1.$$

The complete matching moment supplies $|E|^{-\mathscr E}$. Therefore only $|E|^{-(\mathscr E-\mathscr V)}=|E|^{1-\chi}$ remains. Since a tree has $\chi=0$, this supplies an external factor $|E|$, roughly $n$, which is later killed by Markov's normalization. Nontrivial cycle excess supplies powers of roughly $1/n$.

### D5.4 Keep anisotropy explicit

Using Lemma 11 directly, the residual degree factors, apart from constants and encoding factors, are

$$a^{\mathscr E-L}b^{\mathscr E-\mathscr R}|E|^{-(\mathscr E-\mathscr V)}.$$

Using Corollary 12 instead would produce

$$a^Lb^{\mathscr R}(d-1)^{2(\chi-1)}|E|^{-(\mathscr E-\mathscr V)}.$$

Their quotient is completely explicit. The first divided by the second equals

$$a^{\mathscr E-2L}b^{\mathscr E-2\mathscr R}(d-1)^{2-2\chi}
=\left(\frac ab\right)^{2\mathscr R-\mathscr E}
=\left(\frac ab\right)^{2\psi}.$$

This formula reveals the problem: Corollary 12 discards a signed imbalance factor, not merely a universal constant. A simple path example with $d_1>d_2$ already makes the corollary smaller than Lemma 11.

The paper's subsequent display uses the corollary trajectory and rewrites

$$a^Lb^{\mathscr R}=(ab)^{\mathscr E/2}
\left(\frac ba\right)^\psi a^{1-\chi},$$

using $L=\mathscr E-\mathscr R+1-\chi$. This leads to $(ab)^{\mathscr E/2}=\alpha^{2\mathscr E}$ with $\alpha=(ab)^{1/4}$ in the paper's local notation. A fully independent verification of Equation 26 must repair the transition without assuming that discarded factor is automatically absorbed harmlessly.

**5. Dimensional or type check:** $\mathscr V=L+\mathscr R$ and $\mathscr E=\mathscr V-1+\chi$. Signed powers like $a^{1-\chi}$ are valid algebraic factors, even when negative, but an upper bound cannot casually replace one factor by a smaller one.

**6. Hidden assumptions:** Encoding relies on each individual path being free of more than one cycle. The full circuit may be highly tangled. Degree counts assume no orientation is lost beyond the fixed discovery order.

**7. Intuition:** Almost all actual $n,m$ growth cancels between choosing locations and the probability of matching them. What remains is a base spectral factor per distinct edge, roughly $1/n$ per independent cycle, and subpolynomial encoding overhead.

**8. Failure modes:**

- Interchanging $\chi$ with its appendix-signed inverse makes trees look like they have two cycles.
- Treating Corollary 12 as automatically valid can change biregular anisotropy by $(a/b)^{2\psi}$.
- Figure 5's indexed lengths cannot be used as a consistency check unless its three indexing discrepancies are corrected first.

**9. Numeric check (optional):** Test Lemma 11, Corollary 12, and the quotient identity on several small path and cycle supports. Not run.

**10. Remember this:** The encoding and matching cancellation are the conceptual heart, but the printed Corollary 12 step is a real audit point in the anisotropic computation.

---

## D6. Finish the norm bounds and take the $\ell$th root

**1. Target:** Derive the final probabilistic scales and explain why they produce a vanishing additive spectral error.

**2. Where it appears:** Equations 27 to 36 and Section 5.9, pages 22 to 26.

**3. Inputs:** The claimed moment bound

$$\mathbb E\|\bar B^{(\ell)}\|^{2k}\leq \tau^{2k\ell}n f(n),$$

where up to constants the paper takes

$$f(n)=c_1^{(\log n)^{2/3}}c_6^{(\log n)^{1/3}}
(\log n)^{20(\log n)^{1/3}+6}.$$

Also use the remainder bound with $2k$th moment proportional to $(d-1)^{2k\ell}n^{1-2k}f_R(n)$.

**4. Derivation:**

### D6.1 Parameters

Let $L=\log n$ and choose

$$k=\lfloor L^{1/3}\rfloor,\qquad \ell=\lfloor cL\rfloor,
\qquad g(n)=e^{L^{3/4}}.$$

The path-count logarithm is roughly

$$2k\log O((k\ell+1)^2(\ell+1))
=O(L^{1/3}\log L).$$

Therefore the encoding terms are subpolynomial, and geometric cycle series have ratios $o(1)$.

### D6.2 Why $g(n)$ beats $nf(n)$ after taking $2k$th powers

Compute

$$\log(nf(n))
=L+O(L^{2/3})+O(L^{1/3}\log L).$$

On the other hand,

$$2k\log g(n)=2\lfloor L^{1/3}\rfloor L^{3/4}
\asymp2L^{13/12}.$$

Since $13/12>1$ and also exceeds $2/3$, except for the harmless $\log L$ factor,

$$\frac{nf(n)}{g(n)^{2k}}\longrightarrow0.$$

Markov's inequality now gives

$$\mathbb P\left(\|\bar B^{(\ell)}\|\geq\tau^\ell g(n)\right)
\leq\frac{\mathbb E\|\bar B^{(\ell)}\|^{2k}}
{\tau^{2k\ell}g(n)^{2k}}
\leq\frac{nf(n)}{g(n)^{2k}}=o(1).$$

The logarithmic size $f(n)=o(n^\epsilon)$ alone would be too weak to cancel the leading $n$. The growing exponent inside $k$ is essential.

### D6.3 The remainder scale

The remainder proof uses one deterministic $S$ factor per segment. Across $2k$ trace segments,

$$|S_{ef}|\leq\frac{d-1}{|E|}
\quad\Longrightarrow\quad
\prod_{s=1}^{2k}|S_{e_s f_s}|\leq
\left(\frac{d-1}{|E|}\right)^{2k}.$$

This supplies $n^{-2k}$. The analogous Markov bound therefore has right side $nf_R(n)/g(n)^{2k}$ after multiplying by $n^{2k}$ to form $(d-1)^\ell/n$.

For Section 5.9, apply these moment estimates with constants uniform in $1\leq j\leq\ell$, then use a single union bound over $j$. This gives the simultaneous remainder estimate needed in the sum.

### D6.4 The final root

On the common good event,

$$|\lambda_2(B)|\leq
\left[g(n)\tau^\ell+\ell g(n)\frac{(d-1)^\ell}{n}\right]^{1/\ell}.$$

Now

$$(d-1)^\ell\leq(d-1)^{c\log n}=n^{c\log(d-1)},$$

so choosing $c<1/\log d$, along with the earlier $c<1/32$, makes $(d-1)^\ell/n$ polynomially small. Division by $\tau^\ell$ and multiplication by $\ell$ do not change that for fixed degrees.

Factor out $\tau^\ell$:

$$|\lambda_2(B)|\leq
\tau g(n)^{1/\ell}\left[1+
\ell\frac{(d-1)^\ell}{n\tau^\ell}\right]^{1/\ell}.$$

Both correction factors tend to 1:

$$g(n)^{1/\ell}=\exp\left(\frac{L^{3/4}}{cL+O(1)}\right)
=\exp(O(L^{-1/4}))\to1,$$

and the bracket's $\ell$th root tends to 1 because the bracket is $1+o(1)$. Hence $|\lambda_2(B)|\leq\tau+\epsilon_n$ for some $\epsilon_n\to0$ with high probability.

**5. Dimensional or type check:** $f(n)$ and $g(n)$ are dimensionless. The norm scales as a matrix step count per $\ell$th root, so the main term has spectral units $\tau$, while the second has $(d-1)/n^{1/\ell}$ before comparing to $\tau$.

**6. Hidden assumptions:** The configuration-model estimates must be conditioned on simplicity. A bounded-away-from-zero simplicity probability preserves this $o(1)$ bound. The proof also requires simultaneous tangle-freeness and all remainder-norm events. Most importantly, D6 inherits the preceding Equation 26 derivation, including the unresolved Corollary 12 issue.

**7. Intuition:** The moment order grows slowly enough that circuit entropy remains subpolynomial, but quickly enough that a slightly stretched exponential threshold beats the ambient factor $n$ with overwhelming probability.

**8. Failure modes:** Keeping $k$ fixed would leave an $n$-dependent trace factor after Markov. Taking $g(n)$ polynomial in $n$ may be too coarse for an additive error. Taking the $\ell$th root before bounding the two terms would also obscure which scale dominates.

**9. Numeric check (optional):** Compare the exponents $\log(nf(n))$ and $2k\log g(n)$ for several large symbolic values of $L$. Not run because this is a purely asymptotic calculation and numerical evidence would add little.

**10. Remember this:** The proof's key scale separation is $L^{13/12}$ in the Markov denominator versus only $L$ from the ambient trace. The $\ell$th root later erases the stretched-exponential slack.

---

## D7. Frame eigenvectors and spectral clustering

**1. Target:** Derive class-constant eigenvectors and explain why a common degree multiplier can expose all frame eigenvectors.

**2. Where it appears:** Sections 6.1 to 6.3, especially Theorem 19, pages 27 to 31.

**3. Inputs:** Frame degree matrix $D$, proportions $p_i$, balance $p_iD_{ij}=p_jD_{ji}$, class sizes $n_i=np_i$, frame Markov matrix $R$, and large Markov matrix $P$.

**4. Derivation:** For a frame right eigenvector $Dx=\lambda x$, define the piecewise-constant vector $\tilde x$ on $G$ by $\tilde x_v=x_i$ when $v$ belongs to class $i$. For any such vertex,

$$(A\tilde x)_v
=\sum_j D_{ij}x_j
=\lambda x_i
=\lambda\tilde x_v.$$

Thus $\lambda\in\sigma(A)$ with an explicitly class-constant eigenvector.

The analogous argument for $R$ and $P$ uses normalized degrees. If $d_i=\sum_jD_{ij}$ and $R_{ij}=D_{ij}/d_i$, let $Rx=\lambda x$. For a vertex in class $i$ whose total degree is $d_i$,

$$(P\tilde x)_v
=\frac1{d_i}\sum_jD_{ij}x_j
=\lambda x_i.$$

If $D\to\kappa D$, then both all class degrees and all large-graph degrees scale by $\kappa$, so $R$ is unchanged. The old frame eigenvectors therefore survive with exactly the same eigenvalues. The blockwise bound of Proposition 18 on all other eigenvalues shrinks with $\kappa$ once biregular and regular spectral-gap results apply to all blocks. Choosing $\kappa$ so its right side is below $\min_i|\lambda_i(R)|$ places every nonzero frame eigenvalue ahead of the stochastic remainder in absolute value.

For the two-block example, set $\beta=d_2/d_1<1$. The sharp cited high-degree threshold is

$$d_1>4\frac{1+\beta}{(1-\beta)^2}+o(1),$$

whereas the sufficient spectral condition used here is

$$d_1>\frac4\beta\left(\frac{1+\beta}{1-\beta}\right)^2+o(1).$$

Their ratio is $(1+\beta)/\beta$, exactly the loss factor stated on page 31.

**5. Dimensional or type check:** $\tilde x\in\mathbb R^n$ repeats $x_i$ over $n_i$ vertices. $D$ acts on $\mathbb R^K$ while $A$ acts on $\mathbb R^n$. Row-normalization of $D$ does not change whether $D$ has zero eigenvalues.

**6. Hidden assumptions:** The theorem needs nonzero frame eigenvalues and large enough common degree. Block independence is used in the configuration construction where stated, while Proposition 18 is imported. Negative eigenvalues must be compared by modulus, not signed order.

**7. Intuition:** The frame is the exact quotient of an equitable partition. Class-constant vectors see only the quotient degrees, whereas within-class fluctuations feel the spectral gap of each random block.

**8. Failure modes:** Scaling degrees does not change a zero frame eigenvalue into a nonzero one. Weak assortativity, very small classes, or unbalanced degrees can complicate the common block thresholds. The resulting sufficient condition need not be sharp.

**9. Numeric check (optional):** Form a tiny frame and a regular block graph, then verify that repeating a frame eigenvector preserves its value. Not run.

**10. Remember this:** Frame eigenvectors are exact, not approximate, before any spectral-gap argument begins. The gap only tells you where they sit among all eigenvectors.

---

## D8. Tanner distance substitution and the $(14,9)$ illustration

**1. Target:** Derive the code bound's positive-distance condition and evaluate the example's algebra without overstating its finite-$n$ guarantee.

**2. Where it appears:** Section 7, Theorem 21 through the example, pages 31 to 32.

**3. Inputs:** Janwa-Lal distance bound, local codes $\mathcal C_1=[14,8,7]$, $\mathcal C_2=[9,4,6]$, degrees $d_1=14,d_2=9$, and $n=216,m=336$ for the finite calculation.

**4. Derivation:** Positivity of the deterministic Janwa-Lal bound requires

$$\delta_1\delta_2-\frac\eta2(\delta_1+\delta_2)>0,$$

equivalently

$$\eta<\frac{2\delta_1\delta_2}{\delta_1+\delta_2}.$$

The theorem hypothesis $\delta_2>\eta/2$ alone is not always enough to guarantee that stronger product inequality, though in the present example it is checked consistently.

Ignoring the vanishing spectral term for an asymptotic illustration, substitute $\eta_0=\sqrt{13}+\sqrt8$:

$$\eta_0\approx3.605551+2.828427=6.433978,$$

$$\delta_1\delta_2=42,
\qquad \frac{\eta_0}{2}(\delta_1+\delta_2)
=6.5\eta_0\approx41.820860.$$

The remaining bracket is approximately $0.179140$. Since $n/d_2=216/9=24$, its distance contribution is approximately $24\cdot0.179140=4.2994$.

Therefore the idealized distance contribution is approximately $4.30$. The corresponding exact relative-distance substitution is

$$\frac{\delta}{nd_1}\geq\frac1{d_1d_2}
\left[42-\frac{13}{2}(\sqrt{13}+\sqrt8)\right]
\approx0.0014218,$$

which rounds to the paper's $0.0014$. The rate-bound calculation is

$$\frac{k_1}{d_1}+\frac{k_2}{d_2}-1
=\frac8{14}+\frac49-1
=\frac47+\frac49-1
=\frac{36+28-63}{63}
=\frac1{63}\approx0.0158730.$$

This matches the paper's $0.016$. An integer code distance of at least 4 is therefore consistent with the idealized $\epsilon_n=0$ substitution. With an unknown positive asymptotic error, however, the finite calculation does not itself prove that this particular $n=216$ graph satisfies the needed spectral inequality.

For alphabet consistency, the local codes as described are Reed-Solomon over $\mathbb F_{16}$. Each edge then carries four bits of representation, but the code-distance calculation is naturally in symbols. A separate concatenation argument would be needed to claim a binary Hamming-distance bound at bit level.

**5. Dimensional or type check:** $|E|=nd_1=216\cdot14=3024=336\cdot9$. The relative distance divides $\delta$ by 3024 edge symbols. Multiplying by four bits per symbol is a separate binary encoding choice.

**6. Hidden assumptions:** The positivity condition is essential. Local rates and lengths must be compatible with the field size and symbol ordering at each vertex. The random spectral statement is asymptotic and high probability, not a certificate for one finite drawn graph.

**7. Intuition:** Larger local distances help, but the adjacency second eigenvalue taxes both local constraints. If $\eta$ is too large, the Janwa-Lal lower bound becomes negative and says nothing.

**8. Failure modes:** Do not silently drop $\tilde\epsilon_n$ when moving to finite $n$. Do not interpret the printed unscaled Corollary 22 error as if Theorem 4 supplied a rate. Do not equate symbol distance over $\mathbb F_{16}$ with binary Hamming distance without a binary concatenation analysis.

**9. Numeric check (optional):** The example is concrete and numerically checkable. No script was run. The arithmetic above was derived exactly and decimal values are approximate only.

**10. Remember this:** The theorem gives a positive-distance mechanism. The example illustrates size and scale, not a finite-instance verification. The correct rate calculation is $1/63\approx0.015873$.

---

## D9. Rectangular matrix completion, noiseless and noisy

**1. Target:** Reproduce the constant $4K_G$ in Theorem 24 and the extra $4\delta^2$ in Theorem 25.

**2. Where it appears:** Section 8.2 and 8.3, pages 33 to 35, Equations 41 and 42.

**3. Inputs:** Bipartite expander mixing, sign rank-one matrices, sign nuclear norm $\nu$, comparison $\nu(Z)\leq K_G\gamma_2(Z)$, residual $R=(\hat Y-Y)\circ(\hat Y-Y)$, and optimality of $\hat Y$.

**4. Derivation:**

### D9.1 Rank-one sign discrepancy

Let $u\in\{\pm1\}^n$, $v\in\{\pm1\}^m$, and $S=uv^*$. Define $S'=(S+J)/2$, and let $A$ and $B$ be the positive row and column supports. Then

$$S'=\mathbf1_A\mathbf1_B^*+\mathbf1_{A^c}\mathbf1_{B^c}^*.$$

Since the all-ones matrix has the same global average and sampled average, these cancel, leaving

$$\left|\frac1{nm}\sum_{i,j}S_{ij}-
\frac1{|E|}\sum_{(i,j)\in E}S_{ij}\right|
=2\left|\frac1{nm}\sum S'_{ij}-
\frac1{|E|}\sum_E S'_{ij}\right|.$$

Triangle inequality on the two product sets gives at most twice the two corresponding expander discrepancies. Bipartite expander mixing gives, for $x=|A|/n$ and $y=|B|/m$,

$$\left|\frac1{nm}\sum S_{ij}-\frac1{|E|}\sum_ES_{ij}\right|
\leq\frac{4\eta}{\sqrt{d_1d_2}}\sqrt{xy(1-x)(1-y)}.$$

Because $xy(1-x)(1-y)\leq1/16$, this is at most $\eta/\sqrt{d_1d_2}$.

### D9.2 Extend to general matrices and squared residual

Decompose $Z=\sum_i\alpha_iS^i$ into rank-one sign matrices with $\nu(Z)=\sum_i|\alpha_i|$. Linearity and the triangle inequality give sampling discrepancy at most $\nu(Z)\eta/\sqrt{d_1d_2}$, then Grothendieck's comparison gives at most $K_G\gamma_2(Z)\eta/\sqrt{d_1d_2}$.

For $\Delta=\hat Y-Y$ and $R=\Delta\circ\Delta$, exact fitting in the noiseless case makes $\sum_E r_{ij}=0$. Hence

$$\frac1{nm}\|\Delta\|_F^2
\leq K_G\gamma_2(R)\frac\eta{\sqrt{d_1d_2}}.$$

Now use Hadamard submultiplicativity and the ordinary norm triangle inequality:

$$\gamma_2(R)\leq\gamma_2(\Delta)^2
\leq(\gamma_2(\hat Y)+\gamma_2(Y))^2.$$

The target $Y$ is feasible for the constrained minimization, so $\gamma_2(\hat Y)\leq\gamma_2(Y)$ and therefore

$$\gamma_2(R)\leq4\gamma_2(Y)^2.$$

Substitution proves the noiseless constant $4K_G$.

### D9.3 Add noise

In the noisy program, $Y$ remains feasible because its sampled error equals the noise level. Therefore $\gamma_2(\hat Y)\leq\gamma_2(Y)$ still holds and the same discrepancy estimate applies. Now only the observed residual need not vanish. Instead,

$$\|\mathcal P_E(\hat Y-Y)\|_F
\leq\|\mathcal P_E(\hat Y-Z)\|_F+
\|\mathcal P_E(Z-Y)\|_F
\leq2\delta\sqrt{|E|}.$$

Consequently,

$$\frac1{|E|}\|\mathcal P_E(\hat Y-Y)\|_F^2\leq4\delta^2.$$

Adding this to the full-minus-sampled discrepancy bound proves Theorem 25.

### D9.4 Insert the random-graph gap

Corollary 26 now follows by conditional reasoning: restrict to the high-probability event $\eta\leq\sqrt a+\sqrt b+\epsilon_n$ and apply the deterministic Theorem 24 to every $Y$.

**5. Dimensional or type check:** $Y,\hat Y,Z,R\in\mathbb R^{n\times m}$. $\mathcal P_E$ returns an $n\times m$ matrix supported on sampled entries. The printed sign-vector domain $u,v\in\{\pm1\}^{n\times m}$ must instead be read as separate vectors $u\in\{\pm1\}^n$, $v\in\{\pm1\}^m$.

**6. Hidden assumptions:** The observation graph must satisfy the expander-mixing hypothesis. The norm-comparison constants are for real matrices. The noisy guarantee constrains only sampled mean-square noise, not arbitrary worst-case entries. Existence of a minimizer is assumed by the convex program formulation.

**7. Intuition:** A good expander samples entrywise mean values accurately up to a matrix-complexity tax. Since observed errors are zero or small, most of the total Frobenius error must be small too.

**8. Failure modes:** This is not exact recovery and does not assert low-rank singular values or sampled entry error extrapolate optimally. A graph with a poor gap gives a weak bound. Unmodelled observation bias, such as nonuniform sampling independent of $E$, is outside the theorem.

**9. Numeric check (optional):** Verify the sign-matrix identity and the maximum $xy(1-x)(1-y)=1/16$ on small examples. Not run.

**10. Remember this:** Expanders control density bias, Grothendieck controls factorization complexity, and convex minimality supplies the final factor four. Noise adds a direct sampled-error term, not another spectral factor.
