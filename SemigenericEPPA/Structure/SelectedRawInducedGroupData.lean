import SemigenericEPPA.Structure.InducedEffectiveGeometry
import SemigenericEPPA.Structure.TotalOldRawPalette

/-!
# Raw colour and effective geometry data on a genuine selected subset

The nontrivial-G selected raw flip theorem needs an actual old
effective geometry DS on the selected subset and an everywhere
defined raw reference satisfying phi, reversal and invariance
on real cross-part old edges.

For a literal raw R1--R3 presentation P and an actual raw
automorphism group action rho on S, NONE of these are additional
hypotheses. DS is the induced canonical effective reduct, and
the raw reference is the existing total old colour. Its arbitrary
same-class default is never used.

This packages exactly the three raw assumptions of the
selected indexed witness flip-safety and fixed raw-cover bridge
without imposing self-reversal on any arbitrary raw colour.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w}
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- On the genuine selected subtype S, the canonical effective
reduct and original old raw colours satisfy the precise
phi/reversal/H-invariance equations needed by the projected
raw flip-safety theorem. No raw extension assumption. -/
theorem selectedRawInducedGroupData
    (P : RawRectanglePresentation d A)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hPart : ∀ (h : H) (a b : S),
      P.part (rho h a).val (rho h b).val ↔ P.part a.val b.val)
    (hColour : ∀ (h : H) (a b : S),
      P.colour (rho h a).val (rho h b).val =
        P.colour a.val b.val) :
    let DS : EffectiveGeometry d.s S := P.effectiveReduct.induced S
    let raw : S → S → C :=
      fun a b => P.totalOldRawColour a.val b.val
    (∀ a b : S, ¬DS.part a b →
      d.phi (raw a b) = DS.F a b) ∧
    (∀ a b : S, ¬DS.part a b →
      raw b a = d.reverse (raw a b)) ∧
    (∀ (h : H) (a b : S), ¬DS.part a b →
      raw (rho h a) (rho h b) = raw a b) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro a b hcross
    have hab : ¬P.part a.val b.val := by
      intro hp
      exact hcross ((P.effectiveReduct_part a.val b.val).mpr hp)
    exact P.totalOldRawColour_phi a.val b.val hab
  · intro a b hcross
    have hab : ¬P.part a.val b.val := by
      intro hp
      exact hcross ((P.effectiveReduct_part a.val b.val).mpr hp)
    exact P.totalOldRawColour_reverse a.val b.val hab
  · intro h a b hcross
    have hab : ¬P.part a.val b.val := by
      intro hp
      exact hcross ((P.effectiveReduct_part a.val b.val).mpr hp)
    have hnew : ¬P.part (rho h a).val (rho h b).val := by
      intro hp
      exact hab ((hPart h a b).mp hp)
    have hcolNew :=
      P.totalOldRawColour_cross (rho h a).val (rho h b).val hnew
    have hcolOld := P.totalOldRawColour_cross a.val b.val hab
    rw [hColour h a b] at hcolNew
    exact Option.some.inj (hcolNew.symm.trans hcolOld)

end RawRectanglePresentation

end SemigenericEPPA
