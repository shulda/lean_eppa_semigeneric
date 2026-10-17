import SemigenericEPPA.Structure.EffectiveColour
import AllThoseEPPA.Map

/-!
# Induced rectangle substructures

The three literal rectangle axioms are hereditary on arbitrary vertex
subsets, including the empty set.  The inclusion is an actual
AllThoseEPPA.Structure.Embedding, not merely a set-theoretic injection.

No finiteness assumptions or EPPA theorem are used.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {C : Type u} {V : Type v} {G : Type w} [Group G]

/-- Relational restriction of a generalized semigeneric structure to a
vertex subset. Every relation is pulled back along subtype inclusion. -/
def inducedRectangle (A : Structure (rectangleLanguage C) V)
    (S : Set V) : Structure (rectangleLanguage C) S where
  rel := fun {n} R xs => A.rel R (fun i => (xs i).val)
  func := fun {n} F _ => PEmpty.elim F

/-- Ordered binary tuples commute with forgetting a subtype proof. -/
private theorem pairTuple_val (S : Set V) (x y : S) :
    (fun i : Fin 2 => (pairTuple x y i).val) =
      pairTuple x.val y.val := by
  funext i
  by_cases hi : i.val = 0
  · simp [pairTuple, hi]
  · simp [pairTuple, hi]

@[simp] theorem inducedRectangle_part
    (A : Structure (rectangleLanguage C) V) (S : Set V) (x y : S) :
    partRel (inducedRectangle A S) x y ↔ partRel A x.val y.val := by
  change A.rel (binarySymbol C none) (fun i => (pairTuple x y i).val) ↔
    A.rel (binarySymbol C none) (pairTuple x.val y.val)
  rw [pairTuple_val S x y]

@[simp] theorem inducedRectangle_raw
    (A : Structure (rectangleLanguage C) V) (S : Set V)
    (c : C) (x y : S) :
    rawRel (inducedRectangle A S) c x y ↔
      rawRel A c x.val y.val := by
  change A.rel (binarySymbol C (some c)) (fun i => (pairTuple x y i).val) ↔
    A.rel (binarySymbol C (some c)) (pairTuple x.val y.val)
  rw [pairTuple_val S x y]

/-- The inclusion is a structure embedding with identity language
component. It works for *any* symbol action, because 1 acts trivially. -/
def inducedRectangle_embedding
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V) (S : Set V) :
    Structure.Embedding act (inducedRectangle A S) A where
  lang := 1
  toFun := Subtype.val
  injective := Subtype.val_injective
  map_rel_iff := by
    intro n R xs
    simp only [Language.Action.onRel_one]
    rfl
  map_func := by
    intro n F xs
    exact PEmpty.elim F

namespace IsRectangleStructure

variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- The class K(G,s,φ) is hereditary under induced substructures.
The parameter S can be any subset, including ∅. -/
theorem induced (h : IsRectangleStructure d A) (S : Set V) :
    IsRectangleStructure d (inducedRectangle A S) := by
  refine {
    parts_equiv := ?_
    raw_only_cross := ?_
    cross_unique := ?_
    reverse := ?_
    rectangle := ?_ }
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (inducedRectangle_part A S x x).2 (h.parts_equiv.refl x.val)
    · intro x y hxy
      exact (inducedRectangle_part A S y x).2
        (h.parts_equiv.symm ((inducedRectangle_part A S x y).1 hxy))
    · intro x y z hxy hyz
      exact (inducedRectangle_part A S x z).2
        (h.parts_equiv.trans
          ((inducedRectangle_part A S x y).1 hxy)
          ((inducedRectangle_part A S y z).1 hyz))
  · intro c x y hc hxy
    exact h.raw_only_cross c x.val y.val
      ((inducedRectangle_raw A S c x y).1 hc)
      ((inducedRectangle_part A S x y).1 hxy)
  · intro x y hxy
    have hc : ¬partRel A x.val y.val := by
      intro hpart
      exact hxy ((inducedRectangle_part A S x y).2 hpart)
    obtain ⟨c, hc0, huniq⟩ := h.cross_unique x.val y.val hc
    refine ⟨c, (inducedRectangle_raw A S c x y).2 hc0, ?_⟩
    intro c' hc'
    exact huniq c' ((inducedRectangle_raw A S c' x y).1 hc')
  · intro c x y
    simpa only [inducedRectangle_raw] using
      (h.reverse c x.val y.val)
  · intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    exact h.rectangle x₀.val x₁.val y₀.val y₁.val
      ((inducedRectangle_part A S x₀ x₁).1 hx)
      ((inducedRectangle_part A S y₀ y₁).1 hy)
      c₀₀ c₀₁ c₁₀ c₁₁
      ((inducedRectangle_raw A S c₀₀ x₀ y₀).1 h00)
      ((inducedRectangle_raw A S c₀₁ x₀ y₁).1 h01)
      ((inducedRectangle_raw A S c₁₀ x₁ y₀).1 h10)
      ((inducedRectangle_raw A S c₁₁ x₁ y₁).1 h11)

end IsRectangleStructure
end SemigenericEPPA
