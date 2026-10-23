import SemigenericEPPA.Algebra.DLFRelativeCoverSafeInvolutions
import SemigenericEPPA.Structure.DLFRegularPartInvolutionSafety
import SemigenericEPPA.Structure.ConstantNewPartActualAutGroup

/-!
# All involutions of the faithful finite relative raw cover are SAFE

Let H≤Q be a prescribed locally safe finite group of old raw
automorphisms. The certified relative group cover \widetilde Q
has an injective section of H and kills involutions whose base
projections are not conjugate into H. Involutions projecting into
conjugates of H are safe because the original Q-action preserves
the effective geometry and complete-good-orbit safety is invariant
under conjugacy.

The faithful original R1--R3 realization adjoins a SINGLE regular
new E-class. No action can exchange a vertex in that new class
with an old vertex, and any pair internal to the new class is
E-related. Thus every actually swapped CROSS-E pair under an
upstairs involution belongs to the old raw structure, with
literally the same effective G-colour as before.

This theorem combines those TWO previously certified interfaces,
returning complete-good-orbit safety of all actual upstairs
involutions in the faithful enlarged original language.
No global saturation, normality of H, or commutativity of Q.
The relative safe EPPA step constructing W for arbitrary A≤B
remains a separate mathematical task.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w t
variable {Q : Type u} [Group Q] [Finite Q]
variable {G : Type v} [Group G] {C : Type w}
variable {V : Type t} {d : RawDatum G C}

/-- The FINITE relative group cover's actual faithful regular-class
raw action has the expected local complete-good-orbit safety of
EVERY square-one element exchanging a cross-E pair, assuming
only the prescribed safe H-involutions on the original P.

This is the final finite safety gate AFTER the group cover and
the one-new-class realization. -/
theorem relativeCover_regularRawAction_allInvolutionsSafe
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [LinearOrder (CoverVertex H)]
    [Fintype (CoverEdge H)] [LinearOrder (CoverEdge H)]
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : Q →* Equiv.Perm V)
    (hPart : ∀ (q : Q) (x y : V),
      P.part (rho q x) (rho q y) ↔ P.part x y)
    (hColour : ∀ (q : Q) (x y : V),
      P.colour (rho q x) (rho q y) = P.colour x y)
    (hSafeH : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rho h.val x = y → rho h.val y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y)) :
    ∀ (a : relativeBoundaryCover H), a * a = 1 →
      ∀ (X Y : V ⊕ relativeBoundaryCover H),
        ¬(P.adjoinConstantNewPart
          (R := relativeBoundaryCover H) c0).part X Y →
        sumRawGroupAction
          (relativeCoverOldAction H rho)
          (rawLeftRegularAction (relativeBoundaryCover H)) a X = Y →
        sumRawGroupAction
          (relativeCoverOldAction H rho)
          (rawLeftRegularAction (relativeBoundaryCover H)) a Y = X →
        d.GoodCompleteOrbitAt
          ((P.adjoinConstantNewPart
            (R := relativeBoundaryCover H) c0).effectiveReduct.F X Y) := by
  have hEffE : ∀ (q : Q) (x y : V),
      P.effectiveReduct.part (rho q x) (rho q y) ↔
      P.effectiveReduct.part x y := by
    intro q x y
    exact (P.effectiveReduct_part (rho q x) (rho q y)).trans
      ((hPart q x y).trans (P.effectiveReduct_part x y).symm)
  have hEffF : ∀ (q : Q) (x y : V),
      ¬P.effectiveReduct.part x y →
        P.effectiveReduct.F (rho q x) (rho q y) =
          P.effectiveReduct.F x y := by
    intro q x y hxy
    have hOld : ¬P.part x y := by
      intro hh
      exact hxy ((P.effectiveReduct_part x y).mpr hh)
    have hNew : ¬P.part (rho q x) (rho q y) := by
      intro hh
      exact hOld ((hPart q x y).mp hh)
    exact P.effectiveReduct_equalColour
      (rho q x) (rho q y) x y (hColour q x y) hNew
  have hSafeEff : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬P.effectiveReduct.part x y →
        rho h.val x = y → rho h.val y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y) := by
    intro h htwo x y hxy hxy' hyx'
    apply hSafeH h htwo x y
    · intro hh
      exact hxy ((P.effectiveReduct_part x y).mpr hh)
    · exact hxy'
    · exact hyx'
  have hCover :=
    relativeCover_involutions_preserve_safeOrbits
      H P.effectiveReduct rho hEffE hEffF hSafeEff
  have hOldSafe : ∀ (a : relativeBoundaryCover H), a * a = 1 →
      ∀ (x y : V), ¬P.part x y →
        relativeCoverOldAction H rho a x = y →
        relativeCoverOldAction H rho a y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y) := by
    intro a htwo x y hxy hxy' hyx'
    apply hCover a htwo x y
    · intro hh
      exact hxy ((P.effectiveReduct_part x y).mp hh)
    · exact hxy'
    · exact hyx'
  intro a htwo X Y hCross hSwapX hSwapY
  exact P.adjoinConstantNewPart_swapSafe_of_oldInvolutionSafe
    c0 (relativeCoverOldAction H rho)
    (rawLeftRegularAction (relativeBoundaryCover H))
    hOldSafe a htwo X Y hCross hSwapX hSwapY

end RelativeDLF
end SemigenericEPPA
