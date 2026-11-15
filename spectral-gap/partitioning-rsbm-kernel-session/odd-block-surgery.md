# Odd-block surgery: distribution and untouched-color audit

This note establishes the distributional steps needed for an odd-block-size extension. It does not modify the even-block theorem. Throughout, `d=d1` is fixed and even, `s=d/2`, `n` is even, and `N=n+1` is odd. A root is added with its label fixed in advance.

The odd-vertex surgery itself is a known construction, also used in Hollom–Lichev–Mond–Portier–Wang, [*Approximate Itai–Zehavi Conjecture for Random Graphs*](https://onlinelibrary.wiley.com/doi/full/10.1002/rsa.70095), published September 16, 2026, in its odd-order regular-graph argument. The direct counting proof below is included to make the distributional requirement explicit; the construction is not claimed as new.

## 1. Uniform-simple surgery produces asymptotically uniform odd-size graphs

Let `G` be a uniform simple `d`-regular graph on `[n]`. Let `M_s(G)` be the set of unordered collections of `s` pairwise vertex-disjoint edges of `G`. Choose `E` uniformly from `M_s(G)`, delete all its edges, add root `w=n+1`, and join `w` to all `2s=d` endpoints. Denote the resulting simple `d`-regular graph on `[N]` by `H`.

For every loopless `d`-regular multigraph on `n` vertices, counting edge copies separately, the number of ordered choices of `s` pairwise vertex-disjoint edges is

`(dn/2)^s (1+O(1/n))`,

uniformly in the graph. Indeed, there are `m=dn/2` edges, and after any fixed number of selected edges at most `O_d(1)` edge copies conflict with their endpoints. Since `s` is fixed, the ratio to `m^s` is `1+O(1/n)`. Consequently

`|M_s(G)| = (dn/2)^s/s! * (1+O(1/n))`

uniformly in simple `G` as well.

For a fixed simple `d`-regular graph `H` on `[N]`, a preimage consists of a pairing `pi` of the `d` root-neighbors whose pairs are all nonedges of `H-w`. Add these paired edges to `H-w` to get `G_pi`. Let

`h(H) = #{such valid pairings}`,

so `0<=h(H)<=(d-1)!!`. Its output probability is exactly

`P_output(H) = |G_(n,d)|^(-1) * sum_(pi valid) |M_s(G_pi)|^(-1)`.

By the uniform counting estimate this equals `c_n h(H)(1+O(1/n))`, for a common constant `c_n`. If `H` has no triangle containing the root, its root-neighbors induce an empty graph and `h(H)=(d-1)!!`. A uniform simple fixed-degree regular graph has a triangle through a prescribed root with probability `O(1/N)`; this follows directly by exposing the root and two further edges in the configuration model, then conditioning on simplicity, whose probability is bounded below. Thus, under uniform simple `H`, `h(H)` differs from `(d-1)!!` only with probability `O(1/N)`.

Here is the normalization argument explicitly. Let `mu_N` be uniform on the simple `d`-regular graphs on `[N]`, let `L=(d-1)!!`, and define the probability measure `nu_N` by the density

`d nu_N/d mu_N(H) = h(H)/E_(mu_N) h(H)`.

The root-triangle estimate gives `E_(mu_N)h = L(1-O(1/n))`. Since `0<=h<=L`,

`TV(nu_N,mu_N) <= (L-E_(mu_N)h)/E_(mu_N)h = O(1/n)`.

The output law has mass `c_n h(H)(1+eta_H)`, with `|eta_H|<=C/n` uniformly for all `H` with `h(H)>0`; both measures put zero mass where `h(H)=0`. Normalization of this formula implies that its density relative to `nu_N` is `1+O(1/n)` uniformly on that support. Hence its distance from `nu_N` is also `O(1/n)`. The triangle inequality proves that the total variation distance between the surgery output law and `mu_N` is `O(1/n)`. No assertion about factorization counts is needed.

## 2. Contiguity survives the selection kernel and surgery

For each simple input `G`, attach exactly the same Markov kernel: choose a uniform `s`-edge matching `E`, then perform surgery. If two input graph laws are contiguous, their joint laws with this selected `E`, and their surgery outputs, are contiguous. For example, if an output bad event has conditional input probability `f_n(G)` in `[0,1]`, expectation tending to zero under one input law implies `f_n->0` in probability there by Markov's inequality, then in probability under the other input law by contiguity, and finally in expectation because `f_n` is bounded.

Therefore the known even-size contiguity between the simple matching-union model and the uniform simple regular model can be lifted through this kernel. Combined with Section 1, success with high probability for matching-union surgery transfers to a uniform simple regular graph on odd `N`.

## 3. Sampling colors leaves untouched matchings independent

Generate a colored union `G=M_1+...+M_d` of independent uniform perfect matchings on `[n]`. Multiedges are allowed at this stage and are distinguished by their colors. Independently sample `s` colors `c_j` uniformly from `[d]` and `s` vertices `v_j` uniformly from `[n]`. The `j`th selected oriented edge is

`(v_j, M_(c_j)(v_j))`.

Each oriented colored edge has the same conditional probability `1/(dn)`. Let `V` be the event that these `s` edges are pairwise vertex-disjoint. Conditional on `G,V`, their unordered edge collection `E` is exactly uniform among the `s`-edge matchings in the colored multigraph: every unordered collection occurs with `s! 2^s` ordered orientations.

Uniformly in `G`,

`P(V|G)=1-O(1/n)`.

For instance, after fewer than `s` selected edges the union of their endpoints has bounded size, and the chance that an independently sampled edge meets these vertices is `O(1/n)` because every vertex has exactly `d` colored incident edges. A union bound suffices.

Consequently the joint law of `(G,E)` under the sampling experiment conditioned on `V` differs in total variation by `O(1/n)` from the law obtained by first sampling the original unweighted colored matching union `G` and then choosing a uniform `E` from its `s`-edge matchings. The only reweighting of `G` is proportional to `P(V|G)=1+O(1/n)`.

Most importantly, fix a color pattern `(c_1,...,c_s)`, let `T` be its set of touched colors, and condition on the entire matchings `M_c` for `c in T` and on the selected vertices. The validity event `V` is determined by this conditioned data. The matchings with colors outside `T` remain independent uniform perfect matchings. There are

`r=d-|T| >= d-s=d/2`

such untouched colors. Thus **for even `d>=6`, every color pattern leaves at least three untouched matchings**, exactly within Mészáros Theorem 1.6. Invalid sampling events and the reweighting cost only `O(1/n)` in probability; no moment estimate on the invalid event is required.

After conditioning on the touched data, let `F` be its old-vertex adjacency matrix after deleting the selected edges, and let `u` be the indicator of their `d` endpoints. Then `F 1=(|T| 1-u)`, and the deterministic contribution after surgery is the bordered matrix

```
[ F   u ]
[ u^T 0 ].
```

The remaining random old-vertex adjacency matrix is the sum of the `r>=3` untouched matchings. These identities give the precise conditional input for the separate finite-field calculation.

The order of the last transfer matters. Apply that conditional finite-field calculation first under the original, unconditioned independent colored matchings, in the auxiliary sampling experiment conditioned only on `V`. The uniform conditional bound proves high-probability success there. The `O(1/n)` total variation comparison then gives success under the original colored-union law with the uniform edge-selection kernel. **Only now condition the original union `G` on simplicity**, whose fixed-degree probability is bounded below. This conditioning costs a bounded factor in the already-proved failure probability; no independence or mixing estimate is asserted after it. On a simple `G`, colored edge copies coincide with the ordinary edges, so the selection kernel is exactly the usual uncolored uniform `s`-edge matching kernel. Established simple-law contiguity transfers success to uniform simple even-size `G` with this same kernel. Section 1 then transfers it to uniform simple odd-size `H` in total variation. Apply this sequence to the two independent internal graphs, and fix the prescribed cross matrix throughout.

## 4. Limits of this audit

The same argument with `d=4` allows a pattern touching two colors, leaving only two untouched matchings. Mészáros's `r>=3` theorem cannot be applied to that pattern through this conditioning. The distributional surgery remains valid for `d=4`, but this particular proof of a uniform conditional mixing input does not cover it. No odd-`N`, `d1=4` simplicity theorem is asserted here.
