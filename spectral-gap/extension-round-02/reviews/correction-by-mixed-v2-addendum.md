# Correction to the CORR-1 review

Issue SG-REV-I1. Written 15 November 2026 UTC.

This addendum corrects a transcription defect in Section 2 of correction-by-mixed-v1.md, whose frozen SHA256 is 85e979fb4bdbd66fd9e086c521d5a87e1f26da7fdf822e4e8a20ae7dc128d246. The original review is preserved unchanged.

In the display for $\mathbb EA-\delta$, a plus sign was omitted before $(a-a^2)\epsilon$, and another plus sign was omitted before the $O(m^{-1})$ term. The entire display is to be read as

\[
\mathbb EA-\delta=\left[\frac{a^2-a}{2}+(a-a^2)\epsilon+2a\eta\right]\frac{\lambda}{m}+O(m^{-1})+O(\lambda^2e^{-2\lambda}/m).
\]

At $a=3/2$, its coefficient is

\[
\frac{a^2-a}{2}+(a-a^2)\epsilon+2a\eta
=\frac38-\frac34\epsilon+3\eta
=3\eta+\frac38(1-2\epsilon).
\]

This is the identity used in the subsequent reconstruction and the identity correctly stated in equation (9) of the author proof. That proof retains SHA256 71148f873f45e5c6db0e7535583398712febc6d153874928b1d91701395f2c42.

The correction closes the transcription finding SG-REV-I1. It does not change the review's acceptance verdict, the signed first-correction coefficient, the remainder analysis, or the optimality consequence. Cite the frozen review together with this addendum when using its displayed reconstruction.
