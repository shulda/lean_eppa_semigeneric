import SemigenericEPPA.Structure.Language
import AllThoseEPPA.Map
import Mathlib.Tactic.FinCases

/-!
# Pairwise-criterion for literal structure embeddings

Every relation in the generalized semigeneric language is binary:
the distinguished equivalence E and the family P_c. Accordingly,
an injective map preserving and reflecting E and each P_c is an
*actual* AllThoseEPPA.Structure.Embedding with identity language action.

This theorem makes the exact relational output of the SAP construction
directly consumable by the general EPPA/partial-isomorphism API. It
never invokes any existence theorem from the upstream library.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {C : Type u} {V : Type v} {W : Type w}

/-- Every binary tuple is determined by its two ordered entries. -/
private theorem tuple_eta (xs : Fin 2 → V) :
    pairTuple (xs 0) (xs 1) = xs := by
  funext i
  fin_cases i <;> rfl

/-- The image of an ordered pair under a map is again the ordered pair
of the two images; this is crucial for *binary*, rather than unordered,
raw-colour predicates. -/
private theorem tuple_map (f : V → W) (xs : Fin 2 → V) :
    pairTuple (f (xs 0)) (f (xs 1)) = f ∘ xs := by
  funext i
  fin_cases i <;> rfl

/-- A literal induced embedding is precisely an injective map reflecting
and preserving E and *all* raw-colour predicates P_c. The result is a
genuine embedding in the upstream AllThoseEPPA API, with language
component 1 (not an artificial relabelling of raw colours). -/
def embeddingOfPairwiseEquiv
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V)
    (B : Structure (rectangleLanguage C) W)
    (f : V → W) (hf : Function.Injective f)
    (hE : ∀ x y, partRel B (f x) (f y) ↔ partRel A x y)
    (hP : ∀ c : C, ∀ x y,
      rawRel B c (f x) (f y) ↔ rawRel A c x y) :
    Structure.Embedding act A B where
  lang := 1
  toFun := f
  injective := hf
  map_rel_iff := by
    intro n R xs
    simp only [Language.Action.onRel_one]
    obtain ⟨sym, hn⟩ := R
    subst n
    cases sym with
    | none =>
      have hp := hE (xs 0) (xs 1)
      change
        B.rel (binarySymbol C none) (f ∘ xs) ↔
          A.rel (binarySymbol C none) xs
      simpa only [partRel, tuple_map, tuple_eta] using hp
    | some c =>
      have hp := hP c (xs 0) (xs 1)
      change
        B.rel (binarySymbol C (some c)) (f ∘ xs) ↔
          A.rel (binarySymbol C (some c)) xs
      simpa only [rawRel, tuple_map, tuple_eta] using hp
  map_func := by
    intro n F xs
    exact PEmpty.elim F

/-- In an *existing* upstream embedding with identity language
component, each concrete E predicate is reflected and preserved. -/
theorem embedding_part_iff
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V)
    (B : Structure (rectangleLanguage C) W)
    (f : Structure.Embedding act A B)
    (htrivial : f.lang = 1)
    (x y : V) :
    partRel B (f x) (f y) ↔ partRel A x y := by
  have h := f.map_rel_iff (binarySymbol C none) (pairTuple x y)
  rw [htrivial] at h
  simpa only [Language.Action.onRel_one, partRel,
    tuple_map] using h

/-- Likewise, every raw-colour predicate P_c is preserved and reflected
by a literal (language-identity) embedding. -/
theorem embedding_raw_iff
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V)
    (B : Structure (rectangleLanguage C) W)
    (f : Structure.Embedding act A B)
    (htrivial : f.lang = 1)
    (c : C) (x y : V) :
    rawRel B c (f x) (f y) ↔ rawRel A c x y := by
  have h := f.map_rel_iff (binarySymbol C (some c)) (pairTuple x y)
  rw [htrivial] at h
  simpa only [Language.Action.onRel_one, rawRel,
    tuple_map] using h

end SemigenericEPPA
