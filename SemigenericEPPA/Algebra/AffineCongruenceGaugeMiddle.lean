import SemigenericEPPA.Algebra.CongruenceAction
import SemigenericEPPA.Algebra.Gauge
import Mathlib.Tactic.Group

/-!
# Congruence orbit transport across common gauge middle terms

The positive coherent-EPPA proof for NONTRIVIAL G uses the following
identity: if one actual old cross-part two-cycle has an effective
colour g_* = s(a_*) M a_*, then every effective witness colour
s(a) M a arising from the same multiplier M belongs to the
CONGRUENCE orbit of g_*.

We prove this identity for the ORIGINAL AFFINE anti-involution
s, without assuming s(1)=1 and WITHOUT recentering at a good
raw colour. In particular this works in arbitrary nonabelian
groups with affine shift s(1).

Set b = s(a) (s(a_*))⁻¹. Then
  normalized_s(b) = a_*⁻¹ a
and
  congruence(s,b,s(a_*) M a_*) = s(a) M a.

The second theorem turns this algebra into the exact saturated-good
raw-colour conclusion needed to certify reversal safety for each
cross-witness pair. It is a mathematical gate; existence of the
full effective group action and its pair multiplier remains to
be proved separately.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- The ORIGINAL affine reversal normalizes the conjugating
element s(a)*(s(a_*))^-1 to the old-coordinate displacement
a_*^-1*a. No assumption on the affine shift s(1). -/
theorem AffineAntiInvolution.normalized_swap_multiplier
    (s : AffineAntiInvolution G) (a aStar : G) :
    s.normalized (s a * (s aStar)⁻¹) = aStar⁻¹ * a := by
  unfold AffineAntiInvolution.normalized
  rw [s.map_mul, s.reverse_inv_affine, s.involutive, s.involutive]
  group

/-- The exact common-middle congruence identity of the positive
coherent-EPPA proof, valid WITHOUT recentering and for arbitrary
affine anti-involution on a noncommutative group. -/
theorem congruence_commonGaugeMiddle
    (s : AffineAntiInvolution G)
    (a aStar middle : G) :
    congruence s (s a * (s aStar)⁻¹)
      (s aStar * middle * aStar) =
        s a * middle * a := by
  unfold congruence
  rw [s.normalized_swap_multiplier a aStar]
  group

/-- A single good effective old two-cycle colour s(a_*) M a_*
makes EVERY gauge conjugate s(a) M a good, provided the effective
good set is congruence-saturated. This is precisely the final
orbit-safety implication for a swapped witness cross edge. -/
theorem RawDatum.goodGaugeMiddle_of_saturated
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
    (a aStar middle : G)
    (hGood : d.s aStar * middle * aStar ∈ d.selfReverseEffective) :
    d.s a * middle * a ∈ d.selfReverseEffective := by
  have h : congruence d.s
      (d.s a * (d.s aStar)⁻¹)
      (d.s aStar * middle * aStar) ∈ d.selfReverseEffective :=
    hsat (d.s a * (d.s aStar)⁻¹)
      (d.s aStar * middle * aStar) hGood
  simpa only [congruence_commonGaugeMiddle] using h

end SemigenericEPPA
