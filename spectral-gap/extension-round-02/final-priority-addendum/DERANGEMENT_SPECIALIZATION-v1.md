# Final classical-polynomial attribution

Date: November 14, 2026 Pacific. Scope: a verified known-polynomial identification. This note does not certify historical priority of a mixed extremal theorem or a uniform error profile.

The primary paper is T. Kim, D. S. Kim, G.-W. Jang and J. Kwon, *A note on some identities of derangement polynomials*, Journal of Inequalities and Applications 2018, article 40. The [publisher version](https://link.springer.com/article/10.1186/s13660-018-1636-8) and the downloaded journal PDF were inspected. Equation (2.22), page 9 of 17, defines higher-order derangement polynomials by

$$
(1-t)^{-r}e^{xt}=\sum_{j\ge0}d_j^{(r)}(x)t^j/j!,\qquad r\in\mathbb N.
$$

For the depleted polynomial used in the manuscript, the exact specialization is

$$
\mathcal P_h(n,s)=(-1)^h d_h^{(n-s-h+1)}(-n).
$$

The order n-s-h+1 is a positive integer throughout h+s<=n. To prove the identity, let V have the gamma density with shape n-s-h+1 and unit scale. Expanding the product of h compatible centered indicators after s prescribed matches gives

$$
\mathcal P_h(n,s)
=\sum_{j=0}^h\binom hj(-1)^{h-j}n^j
\frac{(n-s-j)!}{(n-s-h)!}
=\mathbb E(n-V)^h.
$$

The generating function for the moments of V-n is (1-t)^(-(n-s-h+1))e^(-nt). Taking its coefficient of degree h proves the identification. The order depends on h, so this is a degree-by-degree specialization, not equality of two generating functions with a fixed order.

The [symbolic check](check_derangement.py) compares the depleted recurrence with the published finite coefficient formula for h=0 through 12, identically in n,s. All differences vanish in [the saved report](DERANGEMENT_CHECKS-v1.json). These checks corroborate the general identity above.

This identifies a known polynomial family behind the envelope. The inspected definition and subsequent identities do not by themselves establish the maximum over arbitrary cell patterns, multiplicities and independent colors. The manuscript should credit the polynomial identity and describe its finite extremal results separately. The broader classical Whittaker overlap and access limitations remain as recorded in the earlier frozen audits. An additional source download about four-row permanents was not fully assessed before this note, and no exclusion or priority conclusion is drawn from it.
