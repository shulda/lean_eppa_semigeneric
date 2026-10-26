import SemigenericEPPA.Structure.DisjointRawJointEmbedding
import SemigenericEPPA.Structure.RelationalRoundtrip
import SemigenericEPPA.Structure.PairwiseEmbedding

/-!
# Original-relational finite joint embedding

The canonical disjoint union of functional raw rectangles is transported
back to genuine induced embeddings in the ORIGINAL E / ordered R_c
language, with no restrictions on s, G or the good-colour set.

This is the literal JEP component of the Fraisse-age assertion. It is
independent of the (separately formalized) strong amalgamation proof.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

variable {G : Type u} [Group G] {C : Type v}

namespace RawDatum

/-- Exact finite JEP for arbitrary original-language R1--R3 members,
with induced embeddings on both summands. -/
theorem finiteRelationalJEP
    (d : RawDatum G C)
    {X Y : Type (max u v)} [Fintype X] [Fintype Y]
    (A : Structure (rectangleLanguage C) X)
    (B : Structure (rectangleLanguage C) Y)
    (hA : IsRectangleStructure d A)
    (hB : IsRectangleStructure d B) :
    ∃ (W : Type (max u v)) (hW : Fintype W)
      (D : Structure (rectangleLanguage C) W),
      IsRectangleStructure d D ∧
      ∃ (i : Structure.Embedding (rectangleTrivialAction C) A D)
        (j : Structure.Embedding (rectangleTrivialAction C) B D),
        True := by
  classical
  let P := hA.toRawPresentation
  let Q := hB.toRawPresentation
  let c : C := Classical.choose (d.phi_surjective 1)
  let R := P.disjointJoint Q c
  let D := R.toStructure
  have hPartL (x y : X) :
      partRel D (Sum.inl x) (Sum.inl y) ↔
        partRel A x y := by
    change (P.disjointJoint Q c).part (Sum.inl x) (Sum.inl y) ↔
      partRel A x y
    exact Iff.rfl
  have hPartR (x y : Y) :
      partRel D (Sum.inr x) (Sum.inr y) ↔
        partRel B x y := by
    change (P.disjointJoint Q c).part (Sum.inr x) (Sum.inr y) ↔
      partRel B x y
    exact Iff.rfl
  have hRawL (k : C) (x y : X) :
      rawRel D k (Sum.inl x) (Sum.inl y) ↔
        rawRel A k x y := by
    change hA.rawOption x y = some k ↔ rawRel A k x y
    exact hA.rawOption_some_iff k x y
  have hRawR (k : C) (x y : Y) :
      rawRel D k (Sum.inr x) (Sum.inr y) ↔
        rawRel B k x y := by
    change hB.rawOption x y = some k ↔ rawRel B k x y
    exact hB.rawOption_some_iff k x y
  let i : Structure.Embedding (rectangleTrivialAction C) A D :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C)
      A D Sum.inl
      (by intro x y h; exact Sum.inl.inj h)
      hPartL hRawL
  let j : Structure.Embedding (rectangleTrivialAction C) B D :=
    embeddingOfPairwiseEquiv (rectangleTrivialAction C)
      B D Sum.inr
      (by intro x y h; exact Sum.inr.inj h)
      hPartR hRawR
  exact ⟨X ⊕ Y, inferInstance, D,
    R.toStructure_isRectangleStructure, i, j, trivial⟩

end RawDatum
end SemigenericEPPA
