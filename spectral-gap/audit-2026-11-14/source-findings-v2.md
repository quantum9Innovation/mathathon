# Source findings, revision 2

Revision 1 is preserved. This revision adds a distinct denominator counterexample supplied by the integrator and independently checked below.

## SG-S1: equation (62) is false under its stated conditioning

Status: refuted displayed conditional assertion. Proposition 28 itself is not refuted.

Source: Bordenave, [arXiv:1502.04482v4](https://arxiv.org/abs/1502.04482v4), page 38, equation (62). Local source: `../snapshot/reading-sources/friedman-second-eigenvalue-lifts/source/catane-arxiv.tex`, lines 1689 to 1693.

### A. A shared row already reveals the requested cell

For a uniform permutation of four elements, use $y_1=(1,1)$ and $y_2=(1,2)$. Then $a=k=2\le\sqrt4$. At $t=1$, the stated conditioning is

$$\mathcal F_1=\sigma\bigl(\sigma(1),\sigma^{-1}(2)\bigr).$$

On $\{\sigma(1)=1\}$, of probability $1/4$, the actual conditional probability of $M_{11}=1$ is one. The printed event $\Omega_1$ holds because $\sigma(i_2)=j_1$. Equation (62) instead gives zero and asserts an upper bound $1/3$.

Equation (65) also fails for the centered cell on this event, because $3/4>2/3$.

The unconditional centered product is $-1/16$, consistent with Proposition 28 with $a_1=0$ and $b=2$.

### B. Disjoint cells still have the wrong remaining dimension

Use $y_1=(1,1)$ and $y_2=(2,2)$ with the same $n=4$ and $k=2$. Condition on

$$\sigma(2)=3,\qquad\sigma^{-1}(2)=4.$$

This event has probability $1/12$. Two arrows are exposed, namely $2\mapsto3$ and $4\mapsto2$. The remaining rows are $1,3$ and the remaining columns are $1,4$, so

$$\mathbb P(M_{11}=1\mid\mathcal F_1)=\frac12.$$

Neither clause of $\Omega_1$ holds, but the printed denominator is $n_t=4-|\{\sigma(2)\}|=3$. The source therefore gives $1/3$ instead of $1/2$, and its upper bound $1/(n-a+1)=1/3$ fails as well.

### Consequence and repair

There are two issues: an already exposed cell can equal one, and revealing both images and preimages can remove two arrows per other requested cell. Qualifying the formula only by requiring the requested cell to be unrevealed does not repair the denominator.

The replacement proof conditions only on a compatible prescribed set of arrows. The remaining permutation then has exactly $n-r$ rows and columns, without these ambiguities.

## SG-S2: the exact model for the requested estimate

Proposition 11 concerns unrestricted perfect matchings of $dn$ half-edges. Proposition 28 concerns independent uniform permutations associated with base edges. Brito, Dumitriu, and Harris Lemma 7 uses Proposition 28 because the off-diagonal block of the bipartite configuration model is one uniform permutation matrix on $|E|$ elements.

## Scope

The findings are tied to the cited versions. They do not establish failure of either principal spectral theorem. The replacement proof has a separate frozen revision and needs its own mathematical review.
