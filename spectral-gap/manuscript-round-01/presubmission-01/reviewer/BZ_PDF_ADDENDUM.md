# Addendum: local verification of Bordenave and Zhu v1

Checked 15 November 2026 UTC. This addendum supersedes only the local PDF access limitation in Section 3 of INDEPENDENT_SOURCE_REVIEW.md. The frozen review and its existing manifest remain unchanged.

## Source identity and hash

The downloaded file presubmission-01/sources/bordenave-zhu-v1.pdf has 26 pages and SHA256:

    9fb02688bdd3e3cba1663d101aed5ba9704d5bc3779f6192f81eb8f491113b0d

The first page was rendered and visually inspected. It identifies *A second eigenvalue lower bound for the directed configuration model*, by Charles Bordenave and Yizhe Zhu. The margin identifies arXiv:2611.07104v1, dated 4 November 2026. These details agree with the previously checked [version record](https://arxiv.org/abs/2611.07104v1) and [public PDF URL](https://arxiv.org/pdf/2611.07104v1).

## Page 7 visual check

PDF page 7, also printed page 7, was rendered at 150 dpi and inspected in full. The equations and their assumptions are legible. Equation (2.3) appears exactly in the form recorded by the source review:

\[
0\leq\log\frac{N^a}{(N)_a}
=\sum_{h=0}^{a-1}-\log(1-h/N)
\leq\sum_{h=0}^{a-1}\frac{h}{N-a+1}
\leq\frac{a(a-1)}{2(N-a+1)}
\leq\frac12.
\]

The immediately preceding assumption is $a\leq k\leq\sqrt N$. The page also confirms the older singleton factor in equation (2.1), the repeated-edge condition and estimate in equation (2.2), and the affine expansion used in its proof. No transcription discrepancy was found in the earlier assessment of these statements.

Local visual verification and a local PDF hash are now available. The earlier download failure remains an accurate record of that attempt. The broader historical-priority qualification and the substantive contribution assessment are unchanged.

## Preservation check

The frozen review retains SHA256:

    a26458e518ae38ff574956c56adb1fa3c686b6e5bf89fc80ab2b693866d17f32

Its existing reviewer/MANIFEST.json retains SHA256:

    b639e76c65f047c390856f7a97dd73aa7d2b6610101bd83d0adc1dbf4728912a
