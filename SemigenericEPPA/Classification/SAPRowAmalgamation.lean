import SemigenericEPPA.Classification.SAPCornerCompletion

/-!
# Row amalgamation from literal strong amalgamation

Two 2x2 matrices with the same top row are amalgamated over
that top row (and their common two old column vertices).
The *exact overlap* clause of strong amalgamation forces the
two new bottom-row vertices to remain distinct. As they are
E-related to the old row, they form a genuine new 2x2 rectangle,
giving the row-amalgamation law.

No abstraction of SAP into a matrix pushout is assumed.
-/

namespace SemigenericEPPA.Classification

open AllThoseEPPA

namespace RectangleRule

variable {C : Type} (R : RectangleRule C)

/-- Shared base: one row and two ordered column vertices. -/
def rowBase (a b : C) : PUnit → Bool → C
  | _, false => a
  | _, true => b

/-- Inclusion of the common top row in a 2x2 rectangle. -/
private noncomputable def rowTopEmbedding (a b c d : C) :
    Structure.Embedding (rectangleTrivialAction C)
      (R.matrixStructure a (rowBase a b))
      (R.matrixStructure a (squareMatrix a b c d)) :=
  R.matrixEmbedding a
    (fun _ : PUnit => false) (id : Bool → Bool)
    (by intro x y _; exact Subsingleton.elim x y)
    Function.injective_id
    (rowBase a b) (squareMatrix a b c d)
    (by intro x y; cases x; cases y <;> rfl)

private theorem rowEmbedding_inl (a b c d : C) (x : PUnit) :
    R.rowTopEmbedding a b c d (.inl x) = .inl false := by
  rfl

private theorem rowEmbedding_inr (a b c d : C) (y : Bool) :
    R.rowTopEmbedding a b c d (.inr y) = .inr y := by
  rfl

private theorem rowPreservePart
    {V W : Type}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (f : Structure.Embedding (rectangleTrivialAction C) A B)
    (v w : V) (h : partRel A v w) :
    partRel B (f v) (f w) := by
  have hf : f.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  exact (embedding_part_iff (rectangleTrivialAction C) A B f hf v w).mpr h

private theorem rowPreserveRaw
    {V W : Type}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (f : Structure.Embedding (rectangleTrivialAction C) A B)
    (c : C) (v w : V) (h : rawRel A c v w) :
    rawRel B c (f v) (f w) := by
  have hf : f.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  exact (embedding_raw_iff (rectangleTrivialAction C) A B f hf c v w).mpr h

/-- SAP forces the law that two allowed rows with the same
top profile must also form an allowed rectangle together. -/
theorem rowAmalgamation_of_finiteRuleStrongSAP
    (hSAP : R.HasFiniteRuleStrongSAP) :
    R.HasRowAmalgamation := by
  intro a b c d e f hfirst hsecond
  have hBase : IsRuleStructure R (R.matrixStructure a (rowBase a b)) :=
    R.matrixStructure_isRule a (rowBase a b)
      (R.matrixAdmissible_subsingleton_rows (rowBase a b))
  have hLeft : IsRuleStructure R (R.matrixStructure a (squareMatrix a b c d)) :=
    R.matrixStructure_isRule a (squareMatrix a b c d)
      (R.squareMatrix_admissible a b c d hfirst)
  have hRight : IsRuleStructure R (R.matrixStructure a (squareMatrix a b e f)) :=
    R.matrixStructure_isRule a (squareMatrix a b e f)
      (R.squareMatrix_admissible a b e f hsecond)
  let embL := R.rowTopEmbedding a b c d
  let embR := R.rowTopEmbedding a b e f
  obtain ⟨W, hW, T, hT, i, j, sq⟩ :=
    hSAP hBase hLeft hRight embL embR
  letI : Fintype W := hW
  have hcommRow : i (.inl false) = j (.inl false) := by
    have h := sq.commute (.inl PUnit.unit)
    change i (.inl false) = j (.inl false) at h
    exact h
  have hcommCol (y : Bool) :
      i (.inr y) = j (.inr y) := by
    have h := sq.commute (.inr y)
    change i (.inr y) = j (.inr y) at h
    exact h
  have hnewDistinct : i (.inl true) ≠ j (.inl true) := by
    intro he
    obtain ⟨v, hv, _⟩ := (sq.exact_overlap (.inl true) (.inl true)).mp he
    cases v with
    | inl x =>
        have impossible :
            (Sum.inl (true : Bool) : Bool ⊕ Bool) = .inl false := by
          change (Sum.inl (true : Bool) : Bool ⊕ Bool) = .inl false at hv
          exact hv
        cases impossible
    | inr y =>
        have impossible :
            (Sum.inl (true : Bool) : Bool ⊕ Bool) = .inr y := by
          change (Sum.inl (true : Bool) : Bool ⊕ Bool) = .inr y at hv
          exact hv
        cases impossible
  have hpartL : partRel T (i (.inl true)) (i (.inl false)) :=
    rowPreservePart i _ _ (by simp [matrixStructure_part, matrixPart])
  have hpartR : partRel T (j (.inl false)) (j (.inl true)) :=
    rowPreservePart j _ _ (by simp [matrixStructure_part, matrixPart])
  have hpartRows : partRel T (i (.inl true)) (j (.inl true)) := by
    apply hT.parts_equiv.trans hpartL
    rw [hcommRow]
    exact hpartR
  have hpartCols : partRel T (i (.inr false)) (i (.inr true)) :=
    rowPreservePart i _ _ (by simp [matrixStructure_part, matrixPart])
  have hcolsDistinct : i (.inr false) ≠ i (.inr true) := by
    intro he
    exact (by decide :
      (Sum.inr (false : Bool) : Bool ⊕ Bool) ≠ .inr true)
        (i.injective he)
  have hc : rawRel T c (i (.inl true)) (i (.inr false)) :=
    rowPreserveRaw i c _ _ (by rfl)
  have hd : rawRel T d (i (.inl true)) (i (.inr true)) :=
    rowPreserveRaw i d _ _ (by rfl)
  have he' : rawRel T e (j (.inl true)) (j (.inr false)) :=
    rowPreserveRaw j e _ _ (by rfl)
  have hf' : rawRel T f (j (.inl true)) (j (.inr true)) :=
    rowPreserveRaw j f _ _ (by rfl)
  have he : rawRel T e (j (.inl true)) (i (.inr false)) := by
    rw [hcommCol]
    exact he'
  have hf : rawRel T f (j (.inl true)) (i (.inr true)) := by
    rw [hcommCol]
    exact hf'
  exact hT.rectangle
    (i (.inl true)) (j (.inl true))
    (i (.inr false)) (i (.inr true))
    hnewDistinct hcolsDistinct hpartRows hpartCols
    c d e f hc hd he hf

end RectangleRule
end SemigenericEPPA.Classification
