import SemigenericEPPA.Classification.RectangleDisplacements

/-!
# Reconstructed group coordinates for general rectangle rules

Given the elementary row-amalgamation and corner-completion consequences
of strong amalgamation, this module constructs an actual group of
displacement-preserving permutations and a surjection from original
raw colours. The representation theorem is exactly the noncommutative
rectangle difference law, not merely an injection into permutations.

The affine reversal and the structural SAP bridge are separate follow-up
modules.
-/

namespace SemigenericEPPA.Classification

universe u

namespace RectangleRule

variable {C : Type u} (R : RectangleRule C)
variable (hrow : R.HasRowAmalgamation)
variable (hcorner : R.HasCornerCompletion)

/-- The canonical reconstructed group is the group of all permutations
of effective colours that preserve every displacement. -/
abbrev ReconstructedGroup : Type u :=
  (R.toDisplacementSystem hrow hcorner).preservingGroup

/-- Map a raw colour to the unique displacement-preserving translation
sending the chosen raw origin to its effective colour. -/
noncomputable def reconstructedPhi (origin c : C) :
    R.ReconstructedGroup hrow hcorner :=
  (R.toDisplacementSystem hrow hcorner).coordinate
    (Quotient.mk (R.colourSetoid hrow hcorner) origin)
    (Quotient.mk (R.colourSetoid hrow hcorner) c)

/-- Every group element is the translation defined by some raw
colour (surjectivity in the classification theorem). -/
theorem reconstructedPhi_surjective (origin : C) :
    Function.Surjective (R.reconstructedPhi hrow hcorner origin) := by
  let S := R.toDisplacementSystem hrow hcorner
  let e : R.Palette hrow hcorner :=
    Quotient.mk (R.colourSetoid hrow hcorner) origin
  intro g
  obtain ⟨c, hc⟩ :=
    Quotient.exists_rep (((g : S.preservingGroup) : Equiv.Perm _) e)
  refine ⟨c, ?_⟩
  apply S.preserving_eval_injective e
  change (S.translation e
    (Quotient.mk (R.colourSetoid hrow hcorner) c)) e =
    ((g : Equiv.Perm _) e)
  rw [S.translation_anchor]
  exact hc

/-- The raw origin becomes the identity of the reconstructed group. -/
theorem reconstructedPhi_origin_one (origin : C) :
    R.reconstructedPhi hrow hcorner origin origin = 1 := by
  let S := R.toDisplacementSystem hrow hcorner
  let e : R.Palette hrow hcorner :=
    Quotient.mk (R.colourSetoid hrow hcorner) origin
  apply S.preserving_eval_injective e
  change (S.translation e e) e = e
  exact S.translation_anchor e e

/-- The exact group-valued classification formula, *without* a
pre-existing group on raw or effective colours. -/
theorem allowed_iff_reconstructed_difference
    (origin a b c d : C) :
    R.allowed a b c d ↔
      (R.reconstructedPhi hrow hcorner origin a)⁻¹ *
        R.reconstructedPhi hrow hcorner origin b =
      (R.reconstructedPhi hrow hcorner origin c)⁻¹ *
        R.reconstructedPhi hrow hcorner origin d := by
  let S := R.toDisplacementSystem hrow hcorner
  have h :=
    S.displacement_iff_group_difference
      (Quotient.mk (R.colourSetoid hrow hcorner) origin)
      (Quotient.mk (R.colourSetoid hrow hcorner) a)
      (Quotient.mk (R.colourSetoid hrow hcorner) b)
      (Quotient.mk (R.colourSetoid hrow hcorner) c)
      (Quotient.mk (R.colourSetoid hrow hcorner) d)
  exact (R.displacement_eq_iff hrow hcorner a b c d).symm.trans h

/-- The reversal of raw colours descends to an involution of the
reconstructed permutation group. Its anti-affine multiplication law
is proved independently using starred transpose. -/
noncomputable def reconstructedReverse
    (origin : C) (g : R.ReconstructedGroup hrow hcorner) :
    R.ReconstructedGroup hrow hcorner :=
  let S := R.toDisplacementSystem hrow hcorner
  let e : R.Palette hrow hcorner :=
    Quotient.mk (R.colourSetoid hrow hcorner) origin
  S.coordinate e
    (R.paletteReverse hrow hcorner ((g : Equiv.Perm _) e))

/-- Reversal on the group is precisely reversal of its value at
the distinguished palette origin. -/
theorem reconstructedReverse_eval
    (origin : C) (g : R.ReconstructedGroup hrow hcorner) :
    (((R.reconstructedReverse hrow hcorner origin g :
      R.ReconstructedGroup hrow hcorner) : Equiv.Perm _)
      (Quotient.mk (R.colourSetoid hrow hcorner) origin)) =
      R.paletteReverse hrow hcorner
        ((g : Equiv.Perm _)
          (Quotient.mk (R.colourSetoid hrow hcorner) origin)) := by
  exact (R.toDisplacementSystem hrow hcorner).coordinate_anchor
    (Quotient.mk (R.colourSetoid hrow hcorner) origin)
    (R.paletteReverse hrow hcorner
      ((g : Equiv.Perm _) (Quotient.mk (R.colourSetoid hrow hcorner) origin)))

/-- The reconstructed reversal has order two, without assuming that
it fixes the identity of the reconstructed group. -/
theorem reconstructedReverse_involutive
    (origin : C) (g : R.ReconstructedGroup hrow hcorner) :
    R.reconstructedReverse hrow hcorner origin
      (R.reconstructedReverse hrow hcorner origin g) = g := by
  let S := R.toDisplacementSystem hrow hcorner
  let e : R.Palette hrow hcorner :=
    Quotient.mk (R.colourSetoid hrow hcorner) origin
  apply S.preserving_eval_injective e
  change (((R.reconstructedReverse hrow hcorner origin
      (R.reconstructedReverse hrow hcorner origin g)) :
      Equiv.Perm _) e) = ((g : Equiv.Perm _) e)
  rw [R.reconstructedReverse_eval hrow hcorner origin,
    R.reconstructedReverse_eval hrow hcorner origin,
    R.paletteReverse_involutive hrow hcorner]

/-- Equivariance of the raw-colour projection with reconstructed
reversal; the affine multiplication law remains to be established. -/
theorem reconstructedPhi_reverse
    (origin c : C) :
    R.reconstructedPhi hrow hcorner origin (R.reverse c) =
      R.reconstructedReverse hrow hcorner origin
        (R.reconstructedPhi hrow hcorner origin c) := by
  let S := R.toDisplacementSystem hrow hcorner
  let e : R.Palette hrow hcorner :=
    Quotient.mk (R.colourSetoid hrow hcorner) origin
  apply S.preserving_eval_injective e
  change (S.translation e
    (Quotient.mk (R.colourSetoid hrow hcorner) (R.reverse c))) e =
    (((R.reconstructedReverse hrow hcorner origin
      (R.reconstructedPhi hrow hcorner origin c)) :
      Equiv.Perm _) e)
  rw [S.translation_anchor,
    R.reconstructedReverse_eval hrow hcorner origin]
  change (Quotient.mk (R.colourSetoid hrow hcorner) (R.reverse c)) =
    R.paletteReverse hrow hcorner
      ((S.translation e (Quotient.mk (R.colourSetoid hrow hcorner) c)) e)
  rw [S.translation_anchor, R.paletteReverse_mk hrow hcorner c]

end RectangleRule

end SemigenericEPPA.Classification
