import SemigenericEPPA.Algebra.AffineCongruenceGaugeMiddle
import SemigenericEPPA.Algebra.CongruenceAction
import Mathlib.Tactic.Group

/-!
# Good affine skeletons and swapped witness edges with the same old index

For a witness cross-pair with distinct valuation parts q,r but the
SAME old E-index i, the canonical occupied multiplier is 1 and the
fixed-good skeleton K(q,r) is the chosen s-fixed good element g0.
The exact flipped-pair colour is then

  s(a) * g0^(-1) * a,

NOT merely s(a)*g0*a. Its membership in the good set S needs proof.
For affine reversal t=s(1), even the seed at a=1 is t*g0^(-1).

We prove that this seed lies in the congruence orbit of g0:
  congruence(s, t*g0^(-1), g0) = t*g0^(-1)
whenever s(g0)=g0. The common-middle congruence identity then
places every s(a)*g0^(-1)*a in that SAME good orbit, provided S is
globally congruence-saturated.

No s(1)=1, no commutativity or hidden recentering. This is the
precise same-old-index flip-safety input for nontrivial-G coherent
EPPA. It does NOT assert that global saturation holds in the
weaker relative DLF case.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- An s-fixed element g has its affine inverse-skeleton seed
t*g^(-1) in the same genuine congruence orbit as g, where t=s(1).
The multiplication order matters in the nonabelian case. -/
theorem congruence_inverse_fixed_skeleton_seed
    (s : AffineAntiInvolution G)
    (g : G) (hfix : s g = g) :
    congruence s (s 1 * g⁻¹) g = s 1 * g⁻¹ := by
  unfold congruence AffineAntiInvolution.normalized
  rw [s.map_mul, s.reverse_fixed_origin_inv hfix, s.involutive 1]
  group

/-- For a congruence-saturated good set, the seed effective colour
of two swapped witness parts with identical original class index
is good when their skeleton was chosen from a good fixed colour. -/
theorem RawDatum.good_inverseSkeletonSeed_of_saturated
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
    (g : G) (hgood : g ∈ d.selfReverseEffective) :
    d.s 1 * g⁻¹ ∈ d.selfReverseEffective := by
  have hfix : d.s g = g :=
    d.selfReverseEffective_subset_fixed hgood
  have h := hsat (d.s 1 * g⁻¹) g hgood
  rwa [congruence_inverse_fixed_skeleton_seed d.s g hfix] at h

/-- Full swapped-edge safety for a fixed good skeleton g on a pair
of different valuation parts sharing the SAME original E-index.
The witness incidence a is arbitrary. -/
theorem RawDatum.good_swappedSameIndex_of_saturated
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
    (g : G) (hgood : g ∈ d.selfReverseEffective)
    (a : G) :
    d.s a * g⁻¹ * a ∈ d.selfReverseEffective := by
  have hseed : d.s 1 * g⁻¹ * 1 ∈ d.selfReverseEffective := by
    simpa only [mul_one] using
      d.good_inverseSkeletonSeed_of_saturated hsat g hgood
  exact d.goodGaugeMiddle_of_saturated
    hsat a 1 g⁻¹ hseed

end SemigenericEPPA
