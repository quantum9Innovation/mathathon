# Integrator's initial saddle calculation

Status: an exploratory calculation, not an accepted theorem. Recorded November 15 at approximately 04:36 UTC. The calculation below was obtained before the saddle investigator's matching checkpoint arrived. Subsequent review is not fully independent of that checkpoint.

For the accepted generating function F_N(z)=exp(N f(z)), set

$$
f(z)=z/(1-z)+\log(1-z),\qquad f'(z)=z/(1-z)^2.
$$

The positive coefficient saddle solves r f'(r)=k/N. With t=sqrt(k/N), it is exactly r=t/(1+t). The negative stationary point is -t/(1-t), when t<1. For the positive saddle,

$$
Nf(r)-k\log r
=N[t+(t^2-1)\log(1+t)]-k\log t.
$$

The action in brackets expands as

$$
\frac{t^2}{2}+\frac{2t^3}{3}-\frac{t^4}{4}
+\frac{2t^5}{15}-\frac{t^6}{12}+O(t^7).
$$

The local variance is N r(d/dr)(r f'(r))=2k(1+t). A putative positive-saddle formula is therefore

$$
[z^k]F_N(z)\sim
\frac{\exp(Nf(r))r^{-k}}{\sqrt{4\pi k(1+t)}}.
$$

It should hold when k^3/N tends to infinity, including much larger orders than sqrt(N). It cannot be used uniformly at the cubic transition without the competing negative arc. Pair and triple terms give the Fourier damping needed to test the conjecture. Their different parity roles must remain explicit.

After division by the pairing normalization, the action contains -k^2/(4N). Restoring N^k/(N)_k contributes +k^2/(2N), explaining the accepted +k^2/(4N). The next positive action term is 2k^(5/2)/(15N^(3/2)). It predicts a boundary factor exp(2c^(5/2)/15) at k/N^(3/5) tending to c>0.

Unproved here: a uniform relative coefficient estimate, control of the negative arc, odd normalization including the floor convention, and the exact domain of a finite remainder. The saddle investigator independently reported the same action and is preparing a proof. The integrator will challenge the frozen proof rather than treating this agreement as verification.
