UNIFORM DEGREE-TWO COEFFICIENT: PROVED
November 15, 2026

For every fixed 0 < alpha < 1,

  W_path,alpha(epsilon) ~ W_2,alpha(epsilon)
      ~ log^2(1/epsilon)/(2*pi^2).

The upper estimate is quantitative and uniform over every finite
unit-weight path/cycle and every location of the doubled edge:

  N_C(exp(-L)) <= L^2/(2*pi^2) + O_alpha(L^(3/2)).

Main proof: uniform-path-coefficient.tex (compiled PDF alongside it).
Independent written audit: periodization-independent-audit.tex/.pdf.

Uniform upper mechanism:
  * C <= H, whose leverage-measure kernel is K_alpha(log lambda-log eta).
  * On a log interval of length h, periodize K with period T=h+1.
    Fourier truncation has rank 2q+1 and error O_alpha(exp(-4*pi^2*q/T)).
  * Correct the nonzero images using four separated exponentials per j;
    the tail after J terms is O_alpha(exp(-J)), uniform in h.
  * Consequently any measure of mass m on this interval has a rank
      ((h+1)/(2*pi^2)+4)*R + O_alpha(h+1)
    approximant at operator error <= m*exp(-R).
  * Apply this directly to atomic leverage measures on log blocks
    of length sqrt(L). Their tail <= 2*exp(-s/2) comes from the exact
    finite-path/cycle leverage CDF. PSD pinching costs O(sqrt(L)),
    changing log thresholds by only O(log L). Summing triangular
    ranks gives the exact leading coefficient.

The result covers arbitrary simultaneous choices of n(epsilon) and
p(epsilon). No monotonicity of finite-path spectra is asserted. No
Hilbert--Schmidt limit is used for the uniform upper bound. Convergence
is used only for the lower examples, where its direction is valid.

General theorem also proved: for arbitrary finite measures on [0,infinity)
with mu([s,infinity)) <= A exp(-beta*s), the K_alpha operator has count
<= L^2/(4*pi^2*beta) + O_{alpha,A,beta}(L^(3/2)). This coefficient is
sharp by the exponential-density measure and Laptev's theorem. Thus
uniform leverage CDF <= K*delta^beta gives the same upper coefficient
for relative fractional rank-one corrections with bounded baseline
spectrum.

Proof checks:
  * Three independent parallel internal reviews audited the block-rank
    construction and its summation. One written audit is retained.
  * Primary Laptev theorem (pp. 1038-1039), parameter hypotheses, strict
    counting convention, and weighted-Cauchy specialization inspected.
  * DLMF Fourier-transform entry and normalization inspected.
  * LaTeX compiled twice; no warnings or overfull boxes.

All writes were restricted to this directory. Existing papers unchanged.
No persistent goal created. Result reported to source thread
01a1de83-9f52-7581-a342-e5818f1411fd.

ATTRIBUTION FOLLOW-UP
The classical logarithmic-cell/Fourier/off-diagonal method is credited
to Laptev/Widom. The earlier internal note
matmul/uniform-alpha-channel-search.txt, Sections 6-8, already contains
periodization on cells for arbitrary spectral measures, image correction,
and mass optimization for uniform Schatten estimates. These notes do not
claim a new periodization or phase-volume principle. The result recorded
here is the explicit measure-tail count bound, uniform remainder, and
sharp finite-path/cycle specialization. See internal-method-attribution.txt.
