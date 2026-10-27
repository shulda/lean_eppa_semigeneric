import SemigenericEPPA.Classification.RuleMatrixEmbedding

/-!
# Corner completion from literal strong amalgamation

This is Appendix A's second SAP consequence. The proof amalgamates two
independent one-point extensions of a single cross-edge. Everything
is done in the actual binary E/R_c relational language, with prescribed
induced embeddings. No algebraic corner-completion assumption is used.
-/

namespace SemigenericEPPA.Classification

open AllThoseEPPA

namespace RectangleRule

variable {C : Type} (R : RectangleRule C)

/-- A copy of the universal relation and every raw binary predicate is
preserved by any exact original-language induced embedding. -/
private theorem preservePart
    {V W : Type}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (f : Structure.Embedding (rectangleTrivialAction C) A B)
    (v w : V) (hv : partRel A v w) :
    partRel B (f v) (f w) := by
  have hf : f.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  exact (embedding_part_iff (rectangleTrivialAction C) A B f hf v w).mp hv

private theorem preserveRaw
    {V W : Type}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (f : Structure.Embedding (rectangleTrivialAction C) A B)
    (c : C) (v w : V) (hv : rawRel A c v w) :
    rawRel B c (f v) (f w) := by
  have hf : f.lang = 1 := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  exact (embedding_raw_iff (rectangleTrivialAction C) A B f hf c v w).mp hv

/-- The base one-edge matrix. -/
def cornerBase (a : C) : PUnit → PUnit → C :=
  fun _ _ => a

/-- Add one new vertex on the row side, with arbitrary new colour c. -/
def cornerRow (a c : C) : Bool → PUnit → C
  | false, _ => a
  | true, _ => c

/-- Add one new vertex on the column side, with arbitrary new colour b. -/
def cornerCol (a b : C) : PUnit → Bool → C
  | _, false => a
  | _, true => b

/-- The exact inclusion of the single old edge in the new row span. -/
private noncomputable def cornerRowEmbedding (a c : C) :
    Structure.Embedding (rectangleTrivialAction C)
      (R.matrixStructure a (cornerBase a))
      (R.matrixStructure a (cornerRow a c)) :=
  R.matrixEmbedding a
    (fun _ : PUnit => false) (id : PUnit → PUnit)
    (by intro x y _; exact Subsingleton.elim x y)
    Function.injective_id
    (cornerBase a) (cornerRow a c)
    (by intro x y; cases x; cases y; rfl)

/-- The exact inclusion of the single old edge in the new column span. -/
private noncomputable def cornerColEmbedding (a b : C) :
    Structure.Embedding (rectangleTrivialAction C)
      (R.matrixStructure a (cornerBase a))
      (R.matrixStructure a (cornerCol a b)) :=
  R.matrixEmbedding a
    (id : PUnit → PUnit) (fun _ : PUnit => false)
    Function.injective_id
    (by intro x y _; exact Subsingleton.elim x y)
    (cornerBase a) (cornerCol a b)
    (by intro x y; cases x; cases y; rfl)

/-- Strong amalgamation of the unrestricted general-P age forces
the existence of the missing fourth colour, for EVERY triple. -/
theorem cornerCompletion_of_finiteRuleStrongSAP
    (hSAP : R.HasFiniteRuleStrongSAP) :
    R.HasCornerCompletion := by
  intro a b c
  have hBase : IsRuleStructure R (R.matrixStructure a (cornerBase a)) :=
    R.matrixStructure_isRule a (cornerBase a)
      (R.matrixAdmissible_subsingleton_rows (cornerBase a))
  have hRow : IsRuleStructure R (R.matrixStructure a (cornerRow a c)) :=
    R.matrixStructure_isRule a (cornerRow a c)
      (R.matrixAdmissible_subsingleton_columns (cornerRow a c))
  have hCol : IsRuleStructure R (R.matrixStructure a (cornerCol a b)) :=
    R.matrixStructure_isRule a (cornerCol a b)
      (R.matrixAdmissible_subsingleton_rows (cornerCol a b))
  let f := R.cornerRowEmbedding a c
  let g := R.cornerColEmbedding a b
  obtain ⟨W, hW, T, hT, i, j, hsquare⟩ :=
    hSAP hBase hRow hCol f g
  letI : Fintype W := hW
  have hleft : i (.inl false) = j (.inl PUnit.unit) := by
    simpa only [f, g, cornerRowEmbedding, cornerColEmbedding,
      matrixEmbedding_inl] using
      (hsquare.commute (.inl PUnit.unit))
  have hright : i (.inr PUnit.unit) = j (.inr false) := by
    simpa only [f, g, cornerRowEmbedding, cornerColEmbedding,
      matrixEmbedding_inr] using
      (hsquare.commute (.inr PUnit.unit))
  have hneRow : i (.inl false) ≠ i (.inl true) := by
    intro he
    exact (by decide :
      (Sum.inl (false : Bool) : Bool ⊕ PUnit) ≠ .inl true)
        (i.injective he)
  have hneCol : i (.inr PUnit.unit) ≠ j (.inr true) := by
    rw [hright]
    intro he
    exact (by decide :
      (Sum.inr (false : Bool) : PUnit ⊕ Bool) ≠ .inr true)
        (j.injective he)
  have hpartRow : partRel T (i (.inl false)) (i (.inl true)) :=
    preservePart i _ _ (by rfl)
  have hpartCol' : partRel T (j (.inr false)) (j (.inr true)) :=
    preservePart j _ _ (by rfl)
  have hpartCol : partRel T (i (.inr PUnit.unit)) (j (.inr true)) := by
    rw [hright]
    exact hpartCol'
  have ha : rawRel T a (i (.inl false)) (i (.inr PUnit.unit)) :=
    preserveRaw i a _ _ (by rfl)
  have hc : rawRel T c (i (.inl true)) (i (.inr PUnit.unit)) :=
    preserveRaw i c _ _ (by rfl)
  have hb' : rawRel T b (j (.inl PUnit.unit)) (j (.inr true)) :=
    preserveRaw j b _ _ (by rfl)
  have hb : rawRel T b (i (.inl false)) (j (.inr true)) := by
    rw [hleft]
    exact hb'
  have hcross : ¬partRel T (i (.inl true)) (j (.inr true)) := by
    intro hx
    have hbad : partRel T (i (.inl false)) (j (.inr true)) :=
      hT.parts_equiv.trans hpartRow hx
    exact hT.raw_only_cross b _ _ hb hbad
  obtain ⟨d, hd, _⟩ := hT.cross_unique _ _ hcross
  refine ⟨d, ?_⟩
  exact hT.rectangle
    (i (.inl false)) (i (.inl true))
    (i (.inr PUnit.unit)) (j (.inr true))
    hneRow hneCol hpartRow hpartCol
    a b c d ha hb hc hd

end RectangleRule
end SemigenericEPPA.Classification
