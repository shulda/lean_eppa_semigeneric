import SemigenericEPPA.Classification.MatrixRectangles
import SemigenericEPPA.Classification.AffineClassification
import SemigenericEPPA.Structure.FiniteRelationalStrongSAPComplete

/-!
# Arbitrary rectangle predicates in the literal relational E/R_c language

Unlike the already formalized group-valued class, a general rectangle
predicate need not accept degenerate matrices. Consequently an arbitrary
P is imposed ONLY on 2+2 rectangles with distinct row vertices and
distinct column vertices. These are exactly the rectangle constraints
in Appendix A. This distinction is essential for the SAP-to-P converse.

The group-valued reconstructed class satisfies even the degenerate
instances; the equivalence of the two class predicates is established
below, not assumed.
-/

namespace SemigenericEPPA.Classification

open AllThoseEPPA

universe u

variable {C : Type u} {V : Type u}

/-- The unrestricted triangle base (one E-equivalence and a unique raw
colour on every ordered cross-E pair), with *arbitrary* isomorphism-
invariant 2+2 rectangle rule R. No further triangles are forbidden. -/
structure IsRuleStructure
    (R : RectangleRule C)
    (A : Structure (rectangleLanguage C) V) : Prop where
  parts_equiv : Equivalence (partRel A)
  raw_only_cross :
    ∀ c x y, rawRel A c x y → ¬ partRel A x y
  cross_unique :
    ∀ x y, ¬ partRel A x y → ∃! c : C, rawRel A c x y
  reverse :
    ∀ c x y, rawRel A c x y ↔ rawRel A (R.reverse c) y x
  rectangle :
    ∀ x₀ x₁ y₀ y₁,
      x₀ ≠ x₁ → y₀ ≠ y₁ →
      partRel A x₀ x₁ → partRel A y₀ y₁ →
      ∀ a b c d,
        rawRel A a x₀ y₀ →
        rawRel A b x₀ y₁ →
        rawRel A c x₁ y₀ →
        rawRel A d x₁ y₁ →
        R.allowed a b c d

namespace RectangleRule

variable (R : RectangleRule C)
variable (hrow : R.HasRowAmalgamation)
variable (hcorner : R.HasCornerCompletion)

/-- Exact equality of the finite classes defined by the original P
and the reconstructed group law. In the P class the constraints apply
only to genuinely distinct 2+2 rectangles, whereas the group law is
also automatically true when a row or column is repeated. -/
theorem isRuleStructure_iff_reconstructedGroup
    [Nonempty C] (A : Structure (rectangleLanguage C) V) :
    IsRuleStructure R A ↔
      IsRectangleStructure (R.reconstructedRawDatum hrow hcorner
        (Classical.choice ‹Nonempty C›)) A := by
  classical
  constructor
  · intro h
    refine {
      parts_equiv := h.parts_equiv
      raw_only_cross := h.raw_only_cross
      cross_unique := h.cross_unique
      reverse := h.reverse
      rectangle := ?_ }
    intro x₀ x₁ y₀ y₁ hx hy a b c d ha hb hc hd
    by_cases hrows : x₀ = x₁
    · subst x₁
      have hac : a = c :=
        (h.cross_unique x₀ y₀ (h.raw_only_cross a x₀ y₀ ha)).unique ha hc
      have hbd : b = d :=
        (h.cross_unique x₀ y₁ (h.raw_only_cross b x₀ y₁ hb)).unique hb hd
      rw [← hac, ← hbd]
    by_cases hcols : y₀ = y₁
    · subst y₁
      have hab : a = b :=
        (h.cross_unique x₀ y₀ (h.raw_only_cross a x₀ y₀ ha)).unique ha hb
      have hcd : c = d :=
        (h.cross_unique x₁ y₀ (h.raw_only_cross c x₁ y₀ hc)).unique hc hd
      rw [← hab, ← hcd]
      simp
    exact (R.allowed_iff_reconstructedRawDatum hrow hcorner
      (Classical.choice ‹Nonempty C›) a b c d).mp
      (h.rectangle x₀ x₁ y₀ y₁ hrows hcols hx hy
        a b c d ha hb hc hd)
  · intro h
    refine {
      parts_equiv := h.parts_equiv
      raw_only_cross := h.raw_only_cross
      cross_unique := h.cross_unique
      reverse := h.reverse
      rectangle := ?_ }
    intro x₀ x₁ y₀ y₁ _ _ hx hy a b c d ha hb hc hd
    apply (R.allowed_iff_reconstructedRawDatum hrow hcorner
      (Classical.choice ‹Nonempty C›) a b c d).mpr
    exact h.rectangle x₀ x₁ y₀ y₁ hx hy a b c d ha hb hc hd

/-- Finite strong amalgamation in the literal binary language,
with given induced embeddings and an exact strong square.
This does not hide corner completion or row amalgamation. -/
def HasFiniteRuleStrongSAP : Prop :=
  ∀ {X Y Z : Type u}
    [Fintype X] [Fintype Y] [Fintype Z]
    {A : Structure (rectangleLanguage C) X}
    {B : Structure (rectangleLanguage C) Y}
    {D : Structure (rectangleLanguage C) Z},
    IsRuleStructure R A →
    IsRuleStructure R B →
    IsRuleStructure R D →
    ∀ (f : Structure.Embedding (rectangleTrivialAction C) A B)
      (g : Structure.Embedding (rectangleTrivialAction C) A D),
      ∃ (W : Type u) (hW : Fintype W)
        (T : Structure (rectangleLanguage C) W),
        IsRuleStructure R T ∧
        ∃ (i : Structure.Embedding (rectangleTrivialAction C) B T)
          (j : Structure.Embedding (rectangleTrivialAction C) D T),
          StrongSquare
            (fun x : X => f x) (fun x : X => g x)
            (fun y : Y => i y) (fun z : Z => j z)

/-- If the row/corner consequences of SAP hold, the original
unrestricted P-class has *literal* strong amalgamation. Reuses the
certified full original-language SAP of the reconstructed group class. -/
theorem finiteRuleStrongSAP_of_reconstructedGroup
    (hrow : R.HasRowAmalgamation)
    (hcorner : R.HasCornerCompletion)
    [Nonempty C] : R.HasFiniteRuleStrongSAP := by
  classical
  let origin : C := Classical.choice ‹Nonempty C›
  let d := R.reconstructedRawDatum hrow hcorner origin
  have hSAP : d.HasFiniteRelationalStrongSAP :=
    d.finiteRelationalStrongSAP
  intro X Y Z _ _ _ A B D hA hB hD f g
  have hA' : IsRectangleStructure d A :=
    (R.isRuleStructure_iff_reconstructedGroup hrow hcorner A).mp hA
  have hB' : IsRectangleStructure d B :=
    (R.isRuleStructure_iff_reconstructedGroup hrow hcorner B).mp hB
  have hD' : IsRectangleStructure d D :=
    (R.isRuleStructure_iff_reconstructedGroup hrow hcorner D).mp hD
  obtain ⟨W, hW, T, hT, i, j, sq⟩ := hSAP hA' hB' hD' f g
  exact ⟨W, hW, T,
    (R.isRuleStructure_iff_reconstructedGroup hrow hcorner T).mpr hT,
    i, j, sq⟩

end RectangleRule
end SemigenericEPPA.Classification
