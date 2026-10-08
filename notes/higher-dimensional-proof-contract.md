# Genuine 2+1 gauge counterexample: S025 proof contract

The selected target is the explicit counterexample in [higher-dimensional feasibility](higher-dimensional-feasibility.md), following S024's full-report acceptance. This retains the selected implementation contract. Its obligations are now met by the [exact-source GCP certification](higher-dimensional-certification.md); the contract itself is not the verification evidence.

Use `EuclideanSpace ℝ (Fin 3)` for Cartesian points. Define the spatial radius as `sqrt(x^2+y^2)`, the open diamond by `|t|+radius<1`, the closed diamond by the corresponding non-strict inequality, and strict chronology by `q.t-p.t>radius(q-p)`. Define the Lorentz quadratic form `-t^2+x^2+y^2` and its polarized bilinear form. The density class uses smoothness on an open neighborhood of the closed diamond, bounds [1/2,3/2], actual Euclidean Lipschitz constant two and integral one against normalized flat diamond volume. No coordinatewise product chronology is a substitute.

Define actual Lebesgue volume restricted to the diamond, normalization V=2*pi/3, with-density measures, finite iid products and the directed-order pushforward. `PiLp.volume_preserving_ofLp` / `toLp` and `volume_preserving_piFinSuccAbove` connect Cartesian coordinates to a time coordinate and a two-dimensional Euclidean spatial plane. `EuclideanSpace.volume_ball` and Fubini supply the cross-section integral and actual V. Probability normalization must be proved, including that the flat density is in the class.

The explicit Cartesian map and conformal factor are

```text
D_a(p) = (1+a*t)^2-a^2*(x^2+y^2)
F_a(p) = (((t+a)*(1+a*t)-a*(x^2+y^2))/D_a,
          (1-a^2)*x/D_a, (1-a^2)*y/D_a)
Omega_a(p) = (1-a^2)/D_a(p).
```

Prove the denominator positive on the closed diamond for |a|<1. Cartesian formulas treat the axis without dividing by the spatial radius. Derive the radial null identities `(F_a.t ± radius(F_a))=(t±radius+a)/(1+a*(t±radius))`, diamond preservation and inverse F_-a. Smoothness is on the open nonzero-denominator neighborhood, so boundary and axis points are covered.

Prove the actual derivative, its Lorentz pullback and determinant Omega_a^3. Also prove the separation identity `eta(F_a(q)-F_a(p))=Omega_a(p)*Omega_a(q)*eta(q-p)`. Fix a=1/100. Time orientation can be established by continuously deforming the parameter from zero to a (and to -a): for a timelike pair the transformed time difference cannot vanish, by the strict negative quadratic identity. Neither causal preservation nor the Jacobian is an assumed input to the final result.

Use the differentiable change-of-variables theorem with the proved derivative and injectivity. Establish actual measure transport `(F_a)_*mu_0=Omega_-a^3*mu_0`. Derive normalization and rational density bounds. The implemented Lipschitz argument bounds every coordinate difference by its actual Euclidean norm, derives a denominator Lipschitz constant 3/100, and applies an exact reciprocal-cube bound with constant seven. This proves the required global Euclidean Lipschitz condition directly; it does not use a coordinate supremum norm or assume a gradient bound.

Map every iid coordinate through F_a, prove its actual product-law transport and pointwise preservation of the sampled directed order, and derive equality of every finite labeled order law. Pushing through the existing directed-order isomorphism quotient then gives every unlabeled law too. Order-law equality is a conclusion, not a structure field or hypothesis.

The transported density is spatially radial. Define the O(2) action on the spatial plane and prove it preserves the radius. At the interior point (1/2,0,0), the transported density exceeds one; this gives a strictly positive coordinate supremum discrepancy for every spatial orthogonal transformation. Prove the supremum is bounded and the corresponding infimum distance positive, rather than merely checking a single rational value. Finally derive `g_rho_a=F_-a^*g_1` from the actual conformal identity and real-power density coefficient. The obstruction is to the proposed coordinate gauge; these geometries are isometric.

The authoritative gate remains fresh GCP exact-source root/type/axiom acceptance, no added axioms or admitted proofs, retained failures and source/dependency hashes, focused delivery, supplementary checks and task-owned VM cleanup. The published PDF/DOI remains frozen. This target establishes neither a new physical nonidentifiability result nor a higher-dimensional inverse rate.

Remaining to-do list: focused S025 delivery, supplementary CI and cleanup closeout.
