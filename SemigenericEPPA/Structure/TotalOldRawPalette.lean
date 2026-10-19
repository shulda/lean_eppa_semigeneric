import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import Mathlib.Algebra.Group.End

/-!
# A total raw colour reference extending all original cross-part colours

The fixed raw-cover machinery needs an old colour function on all
ordered pairs, although raw colours are only meaningful between
distinct E-classes. Extend the genuine raw presentation by an arbitrary
default on same-class pairs, and prove the exact cross-colour and
reversal equations. No default-colour fixed point is assumed:
the same-class values are NEVER used by these equations.

For any H-action preserving the original functional raw presentation,
the resulting total reference is H-invariant ON CROSS-CLASS PAIRS.
This discharges the raw-colour hypotheses of the positive G=1
fixed-witness action and the fixed-baseline raw-cover lift.
-/

namespace SemigenericEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}
variable {H : Type z} [Group H]

namespace RawRectanglePresentation

/-- Choose the actual unique cross-part raw colour; inside E use
any arbitrary raw colour obtained by surjectivity of phi. -/
noncomputable def totalOldRawColour
    (P : RawRectanglePresentation d V) (x y : V) : C := by
  classical
  exact if hxy : P.part x y then
    Classical.choose (d.phi_surjective 1)
  else
    P.toStructure_isRectangleStructure.chosenRaw x y hxy

/-- Every cross-part reference is EXACTLY the raw colour of P. -/
theorem totalOldRawColour_cross
    (P : RawRectanglePresentation d V) (x y : V)
    (hxy : ¬P.part x y) :
    P.colour x y = some (P.totalOldRawColour x y) := by
  classical
  have h := P.toStructure_isRectangleStructure.chosenRaw_spec x y hxy
  simpa [totalOldRawColour, hxy] using h

/-- Its effective colour is the exact old F, not just gauge-equivalent. -/
theorem totalOldRawColour_phi
    (P : RawRectanglePresentation d V) (x y : V)
    (hxy : ¬P.part x y) :
    d.phi (P.totalOldRawColour x y) =
      P.effectiveReduct.F x y :=
  P.effectiveReduct_crossColour x y
    (P.totalOldRawColour x y) (P.totalOldRawColour_cross x y hxy)

/-- Raw reversal holds on every genuine cross-class pair. -/
theorem totalOldRawColour_reverse
    (P : RawRectanglePresentation d V) (x y : V)
    (hxy : ¬P.part x y) :
    P.totalOldRawColour y x =
      d.reverse (P.totalOldRawColour x y) := by
  have hyx : ¬P.part y x := by
    intro hyx
    exact hxy (P.part_equiv.symm hyx)
  have h := P.colour_reverse x y
  rw [P.totalOldRawColour_cross x y hxy] at h
  have hy := P.totalOldRawColour_cross y x hyx
  rw [h] at hy
  exact Option.some.inj hy

/-- A group preserving the actual raw functional colouring preserves
the total reference on every cross-class pair. No H-invariance of
the arbitrary within-class default is assumed or required. -/
theorem totalOldRawColour_invariant
    (P : RawRectanglePresentation d V)
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ (h : H) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : H) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y)
    (h : H) (x y : V) (hxy : ¬P.part x y) :
    P.totalOldRawColour (rho h x) (rho h y) =
      P.totalOldRawColour x y := by
  have hcross : ¬P.part (rho h x) (rho h y) := by
    intro heq
    exact hxy ((hPart h x y).mp heq)
  have hnew :=
    P.totalOldRawColour_cross (rho h x) (rho h y) hcross
  have hold := P.totalOldRawColour_cross x y hxy
  rw [hColour h x y] at hnew
  exact Option.some.inj (hnew.symm.trans hold)

end RawRectanglePresentation

end SemigenericEPPA
