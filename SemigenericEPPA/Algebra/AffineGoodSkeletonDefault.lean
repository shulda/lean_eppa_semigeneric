import SemigenericEPPA.Algebra.AffineCongruenceGaugeMiddle
import Mathlib.Tactic.Group

/-!
# The correct unrecentered good effective skeleton constant

The manuscript recentres at a genuinely self-reversing effective
colour g0 so that g0 becomes the identity and s(1)=1. If we retain
the ORIGINAL affine anti-involution s and do NOT recenter, simply
using K=g0 as the neutral witness skeleton is not justified by the
reversal-safety argument.

Write t=s(1). For any s-fixed good effective colour g0, the correct
skeleton value is K0=t*g0^(-1), not g0. Then s(K0)=K0, and the
cross-pair effective colour at a swapped witness pair with pair
multiplier 1 is

  gaugeColour(s,a,K0,a)
    = s(a) * K0^(-1) * a
    = congruence(s,s(a),g0).

Thus saturation of the good set transfers the *original good*
effective g0 to every such cross edge, for arbitrary nonabelian G
and arbitrary affine shift t. This is the precise same-old-index
flip safety algebra needed by nontrivial-G coherent EPPA.

This does not yet prove that all required swapped witness edges use
the appropriate neutral multiplier or that the full finite group
action exists.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- Neutral affine witness skeleton corresponding to a chosen
effective colour g, before recentering the group at g. -/
def AffineAntiInvolution.goodSkeletonDefault
    (s : AffineAntiInvolution G) (g : G) : G :=
  s 1 * g⁻¹

/-- The correct unrecentered good skeleton is reversal-fixed when
the underlying effective colour is. This works without s(1)=1. -/
theorem AffineAntiInvolution.goodSkeletonDefault_fixed
    (s : AffineAntiInvolution G) (g : G)
    (hg : s g = g) :
    s (s.goodSkeletonDefault g) = s.goodSkeletonDefault g := by
  unfold AffineAntiInvolution.goodSkeletonDefault
  rw [s.map_mul, s.reverse_inv_affine, s.involutive 1, hg]
  group

/-- The exact effective colour produced by a neutral-multiplier
swap with the chosen good skeleton is in the AFFINE CONGRUENCE
orbit of g, not merely in some unrelated fixed-point locus.
This is valid in arbitrary noncommutative groups. -/
theorem AffineAntiInvolution.goodSkeletonDefault_gauge_congruence
    (s : AffineAntiInvolution G) (g a : G) :
    gaugeColour s a (s.goodSkeletonDefault g) a =
      congruence s (s a) g := by
  unfold gaugeColour AffineAntiInvolution.goodSkeletonDefault
    congruence AffineAntiInvolution.normalized
  rw [s.involutive]
  group

/-- A reversal-fixed good raw effective colour provides a
SWAP-SAFE default skeleton: every neutral-multiplier paired
gauge colour belongs to the good set, assuming full congruence
saturation. This is precisely the same-index branch of the
positive nontrivial-G reversal-safety argument. -/
theorem RawDatum.good_of_goodSkeletonDefault
    (d : RawDatum G C)
    (hsat : d.IsCongruenceSaturated)
    (g0 : G) (hGood : g0 ∈ d.selfReverseEffective)
    (a : G) :
    gaugeColour d.s a (d.s.goodSkeletonDefault g0) a ∈
      d.selfReverseEffective := by
  rw [d.s.goodSkeletonDefault_gauge_congruence]
  exact hsat (d.s a) g0 hGood

end SemigenericEPPA
