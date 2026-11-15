# Source findings, revision 1

## SG-S1: the conditional bound in equation (62) needs repair

Status: exact counterexample to the displayed conditional assertion. This is not a counterexample to Proposition 28.

Source: Bordenave, [arXiv:1502.04482v4](https://arxiv.org/abs/1502.04482v4), page 38, equation (62). The local source is `../snapshot/reading-sources/friedman-second-eigenvalue-lifts/source/catane-arxiv.tex`, lines 1690 to 1694.

Take a uniform permutation of four elements and the two distinct requested cells

$$y_1=(1,1),\qquad y_2=(1,2).$$

Here $a=k=2\le\sqrt4$, so this is within Proposition 28's range. For $t=1$, the source defines

$$\mathcal F_1=\sigma\bigl(\sigma(1),\sigma^{-1}(2)\bigr).$$

On the event $A=\{\sigma(1)=1\}$, of probability $1/4$, the conditional probability of $M_{11}=1$ is one. The event $\Omega_1$ printed in the source also holds on $A$, because the other requested cell has the same row and $\sigma(i_2)=j_1$.

Thus equation (62) gives both a false equality and a false inequality on $A$:

$$1=\mathbb P(M_{11}=1\mid\mathcal F_1)\ne0,
\qquad 1\not\le\frac1{4-2+1}=\frac13.$$

The same example with both cells centered violates the next conditional absolute first-moment estimate, equation (65), since $3/4>2/3$ on $A$.

The missing qualification is that the cell must remain unrevealed. The source applies the bounds to inconsistent cells as well, so merely stating the qualification does not complete that argument. A replacement proof can expand conflicting cells before conditioning, after which every surviving prescribed set is compatible.

The unconditional centered product is nevertheless

$$\mathbb E[(M_{11}-1/4)(M_{12}-1/4)]=-1/16,$$

which is consistent with Proposition 28. Here $a_1=0$ and $b=2$.

## SG-S2: distinguish the two models

Bordenave Proposition 11 treats unrestricted perfect matchings of $dn$ half-edges. Proposition 28 treats independent uniform permutations associated with base edges. The latter is the exact input to Brito, Dumitriu, and Harris Lemma 7, because the off-diagonal block of the bipartite configuration model is one uniform permutation matrix on $|E|$ elements. An explanation of Proposition 11 alone would miss this model identification.

## Scope

These findings concern the cited revisions. They do not assert that the principal spectral theorem is false. The proposed direct proof will have its own frozen revision and review record.
