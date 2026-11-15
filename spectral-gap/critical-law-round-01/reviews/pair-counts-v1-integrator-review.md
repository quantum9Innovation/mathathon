# Integrator reconstruction of the geometric pair process

November 15, 2026. Reviewer: root. Reviewed [pair-counts-v1.md](../probability/pair-counts-v1.md), SHA256 702e3bb0d1c3db39bd2c95208f6c19a7b63814df337dc4b0d4f4edce5ef64c29.

Verdict: accepted. No mathematical correction is required.

Exposure: the reviewer proposed the conditional-host factorial-moment route and independently wrote the effective-operator proof, including overlapping geometry bounds. This reconstruction is not independent discovery or blind review. A separate reviewer has the full probability source for an additional exact-revision audit.

The sphere-count proof needs almost every root to have maximal spheres through the chosen cutoff, not every marked root to have a tree ball. The expected bad-root proportion is O(q^(2R)/n)=o(1). The simultaneous lower and upper sphere counts are valid for all depths through R. Simplicity conditioning is applied only to a nonnegative exploration bound. It is not used to condition an asserted Poisson distribution.

Lemma 3 was reconstructed in detail. An overlapping tuple of distinct coloured edges has v>2b when its union has b nontrivial components. Its spanning-tree embedding bound produces the factor (n Delta p^2)^b(Delta p)^(v-2b), and Delta p<=B_0/m. This proves the uniform O(1/m) overlap contribution. Colours are disjoint edge sets, and falling factorials prevent repeated edges within a colour, so the argument does not miss a two-vertex multiedge pattern.

For all tuples, replacing an overlap's inclusion probability by p_(2h) incurs at most its already bounded contribution. The exact finite-subset probabilities, falling-factorial expansion and p^2=O(1/m) then give the claimed quantitative moment formula. The uniform-integrability and Tonelli generating-function argument identifies the joint independent Poisson law without an unstated moment-determinacy hypothesis.

The random host means converge in probability and are deterministically bounded, so their products converge in expectation. This justifies averaging the conditional moment statement. The intensity d/(2q) includes the factor one half for unordered pairs. Since q^(r_n)=q^(-phi_n)/s, the phase sign and c^(3/2) factor are correct. The cumulative mean and the endpoint phi=1 reindexing also check.

The short marked graph is a matching by the three-vertex sampling bound. Distinct short paths with disjoint marked endpoints cannot intersect on this event: choosing one endpoint within R/2 of an intersection on each path produces a forbidden cross edge. An interior marked vertex similarly creates a wedge. The unequal-length two-walk bound counts only distinct incidence sequences and remains nonnegative before conditioning. Its endpoint sampling factor and sum over lengths give the displayed o(1) probability of multiple short paths. Loop erasure then proves simplicity and geodesicity of the unique path.

The theorem concerns geometric pair counts only. Its own scope correctly withholds any spectral process, localization or historical-priority conclusion.
