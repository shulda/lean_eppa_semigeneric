import SemigenericEPPA.Structure.DLFFaithfulRelativeCoverSafety
import SemigenericEPPA.Structure.ConstantNewPartActualAutGroup
import SemigenericEPPA.Algebra.DLFFiniteRelativeCoverPackage

/-!
# Finite safe split group cover as actual R1--R3 automorphisms

Given a finite group Q acting by true raw automorphisms on P
and a subgroup H of Q whose involutions reverse only complete-good-
orbit cross-pairs, the explicit three-layer F₂-chain cover T has:

* a surjection T → Q and a faithful split copy of H;
* a faithful strict action T → Aut_raw(P ⊕ T), where the new T-summand
  is ONE regular E-class with constant cross colours;
* the same exact old Q-action on the old P-summand;
* every involution of T reversing an actual crossed pair of P ⊕ T
  has a complete good affine congruence orbit.

The target is the full original-language binary raw automorphism
subgroup, not merely a G-valued effective geometry. No appeal to
coherent EPPA, full congruence saturation or normality of H.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w t
variable {Q : Type u} [Group Q] [Finite Q]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type t} {d : RawDatum G C}

/-- The exact finite relative involution-killing cover acts faithfully
by automorphisms of one explicitly enlarged original-language raw
rectangle. Both the projection to Q and the section of H are exact.

The group action extends the original Q-action on the entire old
summand and is globally safe for every order-two element. -/
theorem finiteSafeSplitRawAutPackage
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (P : RawRectanglePresentation d V) (c0 : C)
    (rho : Q →* Equiv.Perm V)
    (hPart : ∀ (q : Q) (x y : V),
      P.part (rho q x) (rho q y) ↔ P.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      P.colour (rho q x) (rho q y) = P.colour x y)
    (hSafeH : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rho h.val x = y → rho h.val y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y)) :
    Finite (relativeBoundaryCover H) ∧
    Function.Surjective (relativeCoverProjection H) ∧
    Function.Injective (relativeCoverSection H) ∧
    ∃ (act : relativeBoundaryCover H →*
        binaryRawAutSubgroup
          (fun x y : V ⊕ relativeBoundaryCover H =>
            (P.adjoinConstantNewPart
              (R := relativeBoundaryCover H) c0).part x y)
          (fun c x y =>
            (P.adjoinConstantNewPart
              (R := relativeBoundaryCover H) c0).colour x y = some c)),
      Function.Injective act ∧
      (∀ (a : relativeBoundaryCover H) (x : V),
        (act a).val (.inl x) =
          .inl (rho (relativeCoverProjection H a) x)) ∧
      (∀ (h : H) (x : V),
        (act (relativeCoverSection H h)).val (.inl x) =
          .inl (rho h.val x)) ∧
      (∀ (a : relativeBoundaryCover H), a * a = 1 →
        ∀ (X Y : V ⊕ relativeBoundaryCover H),
          ¬(P.adjoinConstantNewPart
            (R := relativeBoundaryCover H) c0).part X Y →
          (act a).val X = Y → (act a).val Y = X →
            d.GoodCompleteOrbitAt
              ((P.adjoinConstantNewPart
                (R := relativeBoundaryCover H) c0).effectiveReduct.F X Y)) := by
  classical
  obtain ⟨hFinite, hSurj, hSectionInj, _hSection, _hConj⟩ :=
    finite_relativeCover_allProperties H
  let rhoCover : relativeBoundaryCover H →* Equiv.Perm V :=
    relativeCoverOldAction H rho
  have hPartCover : ∀ (a : relativeBoundaryCover H) (x y : V),
      P.part (rhoCover a x) (rhoCover a y) ↔ P.part x y := by
    intro a x y
    exact hPart (relativeCoverProjection H a) x y
  have hColourCover : ∀ (a : relativeBoundaryCover H) (x y : V),
      P.colour (rhoCover a x) (rhoCover a y) = P.colour x y := by
    intro a x y
    exact hColour (relativeCoverProjection H a) x y
  let act :=
    P.adjoinRegularPartRawAutHom c0 rhoCover hPartCover hColourCover
  refine ⟨hFinite, hSurj, hSectionInj, act, ?_, ?_, ?_, ?_⟩
  · exact P.adjoinRegularPartRawAutHom_injective
      c0 rhoCover hPartCover hColourCover
  · intro a x
    rfl
  · intro h x
    change (Sum.inl
      (rho (relativeCoverProjection H (relativeCoverSection H h)) x) :
        V ⊕ relativeBoundaryCover H) = .inl (rho h.val x)
    rw [relativeCoverProjection_section]
  · intro a ha X Y hCross hXY hYX
    exact relativeCover_regularRawAction_allInvolutionsSafe
      H P c0 rho hPart hColour hSafeH
      a ha X Y hCross hXY hYX

end RelativeDLF
end SemigenericEPPA
