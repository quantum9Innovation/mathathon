# Reconstruction of the weighted and pair-scale extensions

November 15, 2026. Reviewer: root.

Reviewed frozen sources:

- [weighted-extension-v1.md](../obstruction/weighted-extension-v1.md), SHA256 3ffd9f003e3e4c3d94be96a9ff831f666da815e631eed531cdcbf1ba5d0f33d1.
- [pair-scale-v1.md](../obstruction/pair-scale-v1.md), SHA256 272cdb331e73e23aecc36685cb62211c9733d50022e438c6e7fa7f5fb18c505a.

Verdict: accepted. No mathematical finding requires correction.

The reviewer proposed pursuing the weighted and postcritical extensions and supplied their general form, but did not author these proofs. The review is a separate reconstruction with declared prior exposure.

The tree cavity equation gives t_d(d)=1/(d-1) and t_d'(d)=-1/[(d-1)(d-2)]. Substitution into g_d and f_d gives the recorded D_d. With c_d=d(d-2)^2/[3(d-1)], the rescaled positive-pair Schur bound has limit -d(d-1)/3. The distance-sphere count and floor bound give beta_d=d^2(d-2)/[6(d-1)^2]. For d=3 these recover c_3=1/2 and beta_3=3/8 exactly.

The uniform-H assertion uses the operator norm of the actual added-block difference. It holds simultaneously on the same pair event even when H depends on the host. Compactness makes the infimum well defined. Predetermined marks remain essential.

For the scale a=m^2/n, the radius tends to infinity precisely under the stated upper restriction m=o(sqrt(n)). Its neighbourhood collision estimate tends to zero under m/n^(1/4)->infinity. The conditional mean lower bound tends to beta_d/K, and the overlapping-edge variance term tends to zero because m tends to infinity. These calculations prove both displayed probability inequalities. The lower estimate below n^(1/3) is compatible with the larger collective scale, and is not mislabelled as a matching scale there.

In the supercritical range the bounded perturbation contributes H_0/sqrt(m^3/n) after division by a. The proof correctly uses an arbitrary positive threshold margin before taking its limit. This preserves strict inequalities without assuming a continuous random-variable distribution.

The proofs do not supply an upper scale, a critical limit law, or eigenvector localization. Those must be obtained separately if claimed.
