import SemigenericEPPA.Algebra.AffineReversal
import SemigenericEPPA.Algebra.Rectangle
import Mathlib.Tactic.Group

/-!
# Effective group-valued gauge identities

The exact identities (2.5)--(2.7) of the v0.8 manuscript, over an arbitrary
not-necessarily-abelian group.  The affine factor t = s(1) is retained:
there is no implicit assumption that the reversal is an anti-automorphism.

This file proves that (a) gauge colourings obey the rectangle law, (b)
reversal is compatible with the opposite skeleton, and (c) gauge changes
preserve effective colours.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]

/-- The inverse identity for an arbitrary affine anti-involution. -/
theorem AffineAntiInvolution.reverse_inv_affine
    (s : AffineAntiInvolution G) (x : G) :
    s (x⁻¹) = s 1 * (s x)⁻¹ * s 1 := by
  have hp : s (x⁻¹) * (s 1)⁻¹ * s x = s 1 := by
    have h := s.map_mul x (x⁻¹)
    simpa only [mul_inv_cancel] using h.symm
  calc
    s (x⁻¹) =
      (s (x⁻¹) * (s 1)⁻¹ * s x) * (s x)⁻¹ * s 1 := by group
    _ = s 1 * (s x)⁻¹ * s 1 := by rw [hp]

/-- Effective cross-pair colour from two vertex gauges and a skeleton. -/
def gaugeColour (s : AffineAntiInvolution G)
    (left K right : G) : G :=
  s left * K⁻¹ * right

/-- The v0.8 gauge reversal identity, including the affine t-shift. -/
theorem gauge_reverse (s : AffineAntiInvolution G)
    (left K right : G) :
    s (gaugeColour s left K right) =
      gaugeColour s right (s K) left := by
  unfold gaugeColour
  rw [s.map_mul, s.map_mul, s.reverse_inv_affine, s.involutive]
  group

/-- In any two distinct parts, arbitrary vertex-to-part gauge coordinates
define a matrix with the noncommutative rectangle property. -/
theorem gauge_rectangle (s : AffineAntiInvolution G)
    {X : Type v} {Y : Type w} (K : G)
    (left : X → G) (right : Y → G) :
    RectangleLaw (fun x y => gaugeColour s (left x) K (right y)) := by
  apply rectangle_of_rankOne
  refine ⟨(fun x => s (left x) * K⁻¹), right, ?_⟩
  intro x y
  rfl

/-- Equation (2.7): applying vertex multipliers u,v and the corresponding
skeleton change does not change ANY effective cross-pair colour. -/
theorem gauge_change (s : AffineAntiInvolution G)
    (u v K left right : G) :
    gaugeColour s (u * left) (v * K * (s 1)⁻¹ * s u) (v * right) =
      gaugeColour s left K right := by
  unfold gaugeColour
  rw [s.map_mul]
  group

/-- The row/column rectangle equation is also preserved by transposition
and applying the affine reversal; no commutativity or s(1)=1 is needed. -/
theorem rectangle_reverse (s : AffineAntiInvolution G)
    {X : Type v} {Y : Type w} (F : X → Y → G)
    (h : RectangleLaw F) (p : X) (q : Y) :
    RectangleLaw (fun y x => s (F x y)) := by
  have hfac : ∀ x y, F x y = F x q * ((F p q)⁻¹ * F p y) := by
    intro x y
    simpa only [mul_assoc] using factor_of_rectangle F h p q x y
  apply rectangle_of_rankOne
  refine ⟨(fun y => s ((F p q)⁻¹ * F p y)),
    (fun x => (s 1)⁻¹ * s (F x q)), ?_⟩
  intro y x
  change s (F x y) =
    s ((F p q)⁻¹ * F p y) * ((s 1)⁻¹ * s (F x q))
  rw [hfac x y, s.map_mul]
  group

end SemigenericEPPA
