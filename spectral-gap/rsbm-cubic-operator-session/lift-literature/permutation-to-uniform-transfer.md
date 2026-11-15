# A quantitative bridge from oriented permutations to uniform simple 2-factors

This is an elementary change-of-measure lemma, derived here on 2026-11-15.
It does **not** prove the required prescribed-eigenvalue statement in either
model. It quantifies precisely what a sufficiently strong permutation-model
theorem would have to supply.

Let `Q_N` be the uniform distribution on labeled simple 2-regular graphs on
`[N]`. Let `P_N` be the law of `P+P^T` when `P` is a uniform permutation
conditioned to have no cycles of lengths 1 or 2. Let `K(G)` count the cycle
components. Each simple graph `G` has exactly `2^{K(G)}` oriented permutation
representations, so these two laws are not interchangeable.

## Exact likelihood ratio

Define

```
a_N(u) = [z^N] exp(-u z/2-u z^2/4) (1-z)^(-u/2),
b_N(u) = [z^N] exp(-u z-u z^2/2) (1-z)^(-u).
```

The labeled assembly enumeration gives

```
# simple 2-regular graphs = N! a_N(1),
# permutations with no 1- or 2-cycles = N! b_N(1).
```

Consequently, at every simple 2-regular graph,

```
dQ_N/dP_N(G) = b_N(1)/a_N(1) * 2^{-K(G)}.
```

For each fixed `u>0`, coefficient asymptotics at the unique dominant
singularity `z=1` give

```
a_N(u) ~ exp(-3u/4) N^{u/2-1}/Gamma(u/2),
b_N(u) ~ exp(-3u/2) N^{u-1}/Gamma(u).
```

In particular

```
b_N(1)/a_N(1) ~ sqrt(pi) exp(-3/4) sqrt(N).
```

For the independent pair of graphs, write `Q=Q_N tensor Q_N`,
`P=P_N tensor P_N`, and `T=K(G_1)+K(G_2)`. Their exact likelihood ratio is

```
L = dQ/dP = (b_N(1)/a_N(1))^2 2^{-T}
          ~ pi exp(-3/2) N 2^{-T}.
```

The asymptotic constant in the last formula is deterministic and uniform in
the input graphs, since all the graph dependence is the displayed `2^{-T}`.

## Transfer theorem

Put `beta=1-log(2)=0.3068528194...`, with natural logarithms. For every
fixed `delta in (0,1)` and every event `E` in the pair of simple graphs,

```
Q(E) <= C_delta N^{-I(delta)}
        + C N^{beta+delta log(2)} P(E),

I(delta) = delta+(1-delta)log(1-delta) > 0.
```

The constants are independent of `E` and `N` for all sufficiently large
`N`. Therefore any bound

```
P(E) = O(N^{-a})  with  a > 1-log(2)
```

implies `Q(E)=o(1)`, indeed a polynomial bound with a possibly much smaller
positive exponent. One may choose any fixed
`0<delta<min(1,(a-beta)/log(2))` and obtain

```
Q(E) = O(N^{-min(I(delta), a-beta-delta log(2))}).
```

To prove the theorem, use the exact generating functions to get, for fixed
`u>0`,

```
E_Q[u^T] = (a_N(u)/a_N(1))^2 = O_u(N^{u-1}).
```

For `u=1-delta`, Markov's inequality yields

```
Q(T < (1-delta)log N)
 <= O_delta(N^{u-1-(1-delta)log u})
 = O_delta(N^{-I(delta)}).
```

On the complementary event, `L<=C N^{beta+delta log(2)}`. Splitting
`Q(E)=E_P[L 1_E]` according to these events proves the claim.

If a theorem is originally stated for unrestricted uniform permutations,
conditioning away 1- and 2-cycles costs only a bounded factor, since
`b_N(1)->exp(-3/2)>0` in each block. Thus the same sufficient exponent
`a>beta` applies to such a theorem, provided its event reduces to the
desired event on the simple inputs.

## Why an arbitrary high-probability theorem is still insufficient

Under `Q`, `T/log N -> 1` in probability; under `P`, `T/log N -> 2` in
probability. These concentration statements follow directly from the two
probability-generating functions, or their exponential-moment bounds.
This proves asymptotic singularity of the pair laws and rules out a
contiguity argument.

More quantitatively, set
`E_delta={T <= (1+delta)log N}` for a fixed `delta in (0,1)`. Then
`Q(E_delta)->1`. Under `P`, using `s=(1+delta)/2` and the permutation cycle
generating function gives

```
P(E_delta)
 <= C_delta N^{-J(delta)},
J(delta) = 1-delta+(1+delta)log((1+delta)/2).
```

As `delta->0`, `J(delta)->beta`. Hence for every fixed `a<beta`, there are
events with `P(E)=O(N^{-a})` but `Q(E)->1`. The threshold `beta` is thus
sharp as a universal strict-exponent transfer criterion (this sentence
makes no claim about the borderline exponent exactly `beta`).

## Application target, still open

For

```
A = [[P_1+P_1^T,I],[I,P_2+P_2^T]],
```

with two independent uniform permutations, a bound stronger than
`N^{-(1-log 2)}` on the probability of an extra eigenvector at eigenvalue 1
would suffice to prove the required uniform-simple-2-factor theorem.
Neither strong asymptotic freeness nor a mesoscopic local law supplies
that prescribed-point probability estimate.
