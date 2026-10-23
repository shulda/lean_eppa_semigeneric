import SemigenericEPPA.Structure.ConstantNewPartRawGroupAction
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Relative-cover safety survives adding the faithful regular raw E-class

To realize a finite relative group cover faithfully, one adjoins
ONE new E-class carrying the left regular action of the group.
The group acts on old vertices via the prescribed projection,
and on the new class regularly. The disjoint-sum action preserves
both summands setwise, so it cannot exchange a new point with
an old one. Any two new points belong to the same E-class.

Therefore every group-swapped CROSS-E pair in the enlarged raw
structure lies entirely in the original old carrier. Its
effective colour is exactly the original old effective colour,
because the raw edge colour was preserved LITERALLY.

We prove the exact preservation of complete-good-orbit safety
under this one-class extension. An involution on the new group
need not act faithfully on the old part: the regular new class
handles faithfulness without creating new swapped cross-E edges.

This lemma does not construct the safe relative EPPA witness;
it is the required final safety check after the finite cover
group has already been constructed and realized faithfully.
-/

namespace SemigenericEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {R : Type z} {T : Type t} [Group T]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The canonical effective colour of an OLD cross-E pair is
literally unchanged by adjoining a constant-colour new E-class.
This does not require any assumption on the size of the new
class or on the chosen raw colour c0. -/
theorem adjoinConstantNewPart_old_effectiveCross
    (P : RawRectanglePresentation d V)
    (c0 : C) (x y : V) (hxy : ¬P.part x y) :
    (P.adjoinConstantNewPart (R := R) c0).effectiveReduct.F
      (.inl x) (.inl y) = P.effectiveReduct.F x y := by
  have hSome : ∃ c : C, P.colour x y = some c := by
    cases hc : P.colour x y with
    | none => exact False.elim (hxy ((P.colour_none_iff x y).mp hc))
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c,hc⟩ := hSome
  have hNew :
      (P.adjoinConstantNewPart (R := R) c0).colour
        (.inl x) (.inl y) = some c := by
    simpa only [P.adjoinConstantNewPart_old_colour] using hc
  calc
    (P.adjoinConstantNewPart (R := R) c0).effectiveReduct.F
      (.inl x) (.inl y) = d.phi c :=
      ((P.adjoinConstantNewPart (R := R) c0).effectiveReduct_crossColour
        (.inl x) (.inl y) c hNew).symm
    _ = P.effectiveReduct.F x y :=
      P.effectiveReduct_crossColour x y c hc

/-- If original involutions are good-orbit safe on old cross-E
pairs, the SUM action (old action plus ANY new-class action)
inherits safety of every swapped cross-E pair on the enlarged
actual R1--R3 geometry. The additional class is automatically
harmless because it is invariant and internally one E-class. -/
theorem adjoinConstantNewPart_swapSafe_of_oldInvolutionSafe
    (P : RawRectanglePresentation d V) (c0 : C)
    (rho : T →* Equiv.Perm V)
    (lambda : T →* Equiv.Perm R)
    (hSafe : ∀ (h : T), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rho h x = y → rho h y = x →
        d.GoodCompleteOrbitAt (P.effectiveReduct.F x y))
    (h : T) (hTwo : h * h = 1)
    (X Y : V ⊕ R)
    (hCross : ¬(P.adjoinConstantNewPart (R := R) c0).part X Y)
    (hSwapX : sumRawGroupAction rho lambda h X = Y)
    (hSwapY : sumRawGroupAction rho lambda h Y = X) :
    d.GoodCompleteOrbitAt
      ((P.adjoinConstantNewPart (R := R) c0).effectiveReduct.F X Y) := by
  cases X with
  | inl x =>
      cases Y with
      | inl y =>
          have hxy : ¬P.part x y := hCross
          have hx : rho h x = y :=
            Sum.inl.inj (by simpa only [sumRawGroupAction_inl] using hSwapX)
          have hy : rho h y = x :=
            Sum.inl.inj (by simpa only [sumRawGroupAction_inl] using hSwapY)
          have hs := hSafe h hTwo x y hxy hx hy
          simpa only [P.adjoinConstantNewPart_old_effectiveCross c0 x y hxy]
            using hs
      | inr y =>
          have h : (Sum.inl (rho h x) : V ⊕ R) = .inr y := by
            simpa only [sumRawGroupAction_inl] using hSwapX
          cases h
  | inr x =>
      cases Y with
      | inl y =>
          have h : (Sum.inr (lambda h x) : V ⊕ R) = .inl y := by
            simpa only [sumRawGroupAction_inr] using hSwapX
          cases h
      | inr y =>
          exact False.elim (hCross trivial)

end RawRectanglePresentation
end SemigenericEPPA
