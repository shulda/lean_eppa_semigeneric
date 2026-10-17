import SemigenericEPPA.Structure.Language
import AllThoseEPPA.Map
import Mathlib.Tactic.FinCases

/-!
# Reindexing and exact induced maps of rectangle structures

All relation symbols in the literal language are binary, and there
are no functions. Pulling back every relation along ANY vertex map
produces another R1–R3 structure whenever the target satisfies R1–R3.

If the vertex map is injective, it is an actual identity-language
Structure.Embedding into the original structure. This is the basic
renaming/restriction primitive required to iterate the one-point SAP
construction on arbitrary finite diagrams.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {C : Type u} {V : Type v} {W : Type w}

/-- The full relational pullback along an arbitrary vertex map.
The map need not be injective; the pulled-back E automatically includes
the kernel of the map, and raw colours remain absent on its E-pairs. -/
def pullbackRectangle
    (A : Structure (rectangleLanguage C) V) (f : W → V) :
    Structure (rectangleLanguage C) W where
  rel := fun {_n} R xs => A.rel R (f ∘ xs)
  func := by
    intro n F xs
    exact PEmpty.elim F

@[simp] theorem pullback_partRel
    (A : Structure (rectangleLanguage C) V) (f : W → V)
    (x y : W) :
    partRel (pullbackRectangle A f) x y ↔ partRel A (f x) (f y) := by
  change A.rel (binarySymbol C none) (f ∘ pairTuple x y) ↔
    A.rel (binarySymbol C none) (pairTuple (f x) (f y))
  have ht : (f ∘ pairTuple x y) = pairTuple (f x) (f y) := by
    funext i
    fin_cases i <;> rfl
  rw [ht]

@[simp] theorem pullback_rawRel
    (A : Structure (rectangleLanguage C) V) (f : W → V)
    (c : C) (x y : W) :
    rawRel (pullbackRectangle A f) c x y ↔
      rawRel A c (f x) (f y) := by
  change A.rel (binarySymbol C (some c)) (f ∘ pairTuple x y) ↔
    A.rel (binarySymbol C (some c)) (pairTuple (f x) (f y))
  have ht : (f ∘ pairTuple x y) = pairTuple (f x) (f y) := by
    funext i
    fin_cases i <;> rfl
  rw [ht]

variable {G : Type z} [Group G] {d : RawDatum G C}

/-- Every R1–R3 axiom survives full induced reindexing. In particular,
empty carriers, arbitrary finite bijections, and non-surjective
renaming maps require no separate mathematical assumptions. -/
theorem IsRectangleStructure.pullback
    {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) (f : W → V) :
    IsRectangleStructure d (pullbackRectangle A f) := by
  refine {
    parts_equiv := ?_
    raw_only_cross := ?_
    cross_unique := ?_
    reverse := ?_
    rectangle := ?_ }
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (pullback_partRel A f x x).2 (h.parts_equiv.refl (f x))
    · intro x y hxy
      exact (pullback_partRel A f y x).2
        (h.parts_equiv.symm ((pullback_partRel A f x y).1 hxy))
    · intro x y z hxy hyz
      exact (pullback_partRel A f x z).2
        (h.parts_equiv.trans
          ((pullback_partRel A f x y).1 hxy)
          ((pullback_partRel A f y z).1 hyz))
  · intro c x y hc he
    exact h.raw_only_cross c (f x) (f y)
      ((pullback_rawRel A f c x y).1 hc)
      ((pullback_partRel A f x y).1 he)
  · intro x y hxy
    have hcross : ¬partRel A (f x) (f y) := by
      intro hp
      exact hxy ((pullback_partRel A f x y).2 hp)
    obtain ⟨c, hc, huniq⟩ := h.cross_unique (f x) (f y) hcross
    refine ⟨c, (pullback_rawRel A f c x y).2 hc, ?_⟩
    intro c' hc'
    exact huniq c' ((pullback_rawRel A f c' x y).1 hc')
  · intro c x y
    simpa only [pullback_rawRel] using h.reverse c (f x) (f y)
  · intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    exact h.rectangle (f x₀) (f x₁) (f y₀) (f y₁)
      ((pullback_partRel A f x₀ x₁).1 hx)
      ((pullback_partRel A f y₀ y₁).1 hy)
      c₀₀ c₀₁ c₁₀ c₁₁
      ((pullback_rawRel A f c₀₀ x₀ y₀).1 h00)
      ((pullback_rawRel A f c₀₁ x₀ y₁).1 h01)
      ((pullback_rawRel A f c₁₀ x₁ y₀).1 h10)
      ((pullback_rawRel A f c₁₁ x₁ y₁).1 h11)

/-- Any injective reindexing is an actual upstream identity-language
embedding, which can be composed with other structure embeddings. -/
def pullbackRectangle_embedding
    {Γ : Type*} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V)
    (f : W → V) (hf : Function.Injective f) :
    Structure.Embedding act (pullbackRectangle A f) A where
  lang := 1
  toFun := f
  injective := hf
  map_rel_iff := by
    intro n R xs
    simp only [Language.Action.onRel_one]
    rfl
  map_func := by
    intro n F xs
    exact PEmpty.elim F

/-- Relabelling a rectangle structure along a bijection is
class-preserving and produces an embedding with that exact map. -/
def pullbackRectangle_equiv_embedding
    {Γ : Type*} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V)
    (e : W ≃ V) :
    Structure.Embedding act (pullbackRectangle A e) A :=
  pullbackRectangle_embedding act A e e.injective

end SemigenericEPPA
