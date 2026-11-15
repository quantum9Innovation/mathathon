# A PSD normalized response need not be a graph Laplacian

**Proposition (elementary exact obstruction).** For every fixed 0<α<1,
start with the unweighted path on vertices 1,2,3,4 and double edge {1,2}.
The normalization-aware response

    ΔH=Hα(L',D')−Hα(L,D)

is positive semidefinite and has zero row sums, but ΔH₃₄>0. In particular,
it is not a nonnegative weighted graph Laplacian. This excludes an
interpretation of this PSD response as merely adding nonnegative graph
edges. It does not exclude approximating the full updated form by a graph
sparsifier, or using general PSD low-rank factors.

**Proof.** Give the first edge weight w>0, leave the other two weights one,
write a=1+t>1, and form K_t(w)=L_(w,1,1)+tD_(w,1,1). This is the tridiagonal
matrix with diagonal (wa,(w+1)a,2a,a) and offdiagonal (−w,−1,−1).
Eliminating vertex 1 leaves the effective diagonal at vertex 2

    b₂(w)=a+w(a−1/a),

which strictly increases with w. Eliminating vertex 2 then leaves the
effective diagonal at vertex 3

    b₃(w)=2a−1/b₂(w),

which also strictly increases with w. The inverse on vertices 3,4 is the
inverse of [[b₃,−1],[−1,a]], so

    [K_t(w)^(-1)]₃₄ =1/[a b₃(w)−1]

strictly decreases with w for every t>0. Since d₃=2 and d₄=1 are unchanged,
the positive-power integrand F_t=D−tDK_t^(-1)D satisfies

    [F_t(w)]₃₄ =−2t/[a b₃(w)−1],

which strictly increases with w. The exact identity

    Hα=cα ∫₀∞ t^(α−1) F_t dt,  cα=sin(πα)/π>0,

has convergent endpoint integrals. Integrating its entrywise strict
inequality between w=1 and w=2 proves ΔH₃₄>0. Joint monotonicity of the
operator geometric mean, or the parent note's positive three-column
resolvent response, gives ΔH≥0. Both forms annihilate constants. ∎

Dense corroboration at α=1/2 gives ΔH₃₄≈0.02807335. The proof above, not
the decimal computation, covers every exponent in (0,1).

The underlying scalar power integral and Schur-complement network
interpretation are classical; see [Kubo–Ando, *Means of positive linear
operators*](https://doi.org/10.1007/BF01371042) and [Dörfler–Bullo, *Kron
Reduction of Graphs with Applications to Electrical
Networks*](https://arxiv.org/abs/1102.2950). This proposition's historical
priority has not been established.
