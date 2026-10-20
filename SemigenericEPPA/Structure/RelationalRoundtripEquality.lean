import SemigenericEPPA.Structure.RelationalRoundtrip

/-!
# The functional/relational round trip is actual Lean structure equality

Previously the raw presentation obtained from any relational
rectangle structure was known to preserve and reflect each literal
E and P_c predicate. For a language with NO function symbols,
pointwise equality of those predicates determines the entire
Structure object, not just an isomorphic representation.

We prove this exact equality, so later coherent-EPPA statements
for functional RawRectanglePresentation transport DIRECTLY to
arbitrary original relational structures satisfying R1--R3,
without rebuilding PartialEquiv or the coherence law.

The result does not add any new mathematical condition on the
original relational structure.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) V}

/-- Two structures in the rectangle language are literally equal
if they interpret ALL E and ordered P_c predicates equally.
There are no function symbols to check. -/
theorem rectangleStructure_eq_of_rel_iff
    (X Y : Structure (rectangleLanguage C) V)
    (h : ∀ {n : ℕ}
      (R : (rectangleLanguage C).RelSymbol n)
      (xs : Fin n → V),
      X.rel R xs ↔ Y.rel R xs) :
    X = Y := by
  cases X with
  | mk relX funcX =>
    cases Y with
    | mk relY funcY =>
      have hr : relX = relY := by
        funext n R xs
        exact propext (h R xs)
      have hf : funcX = funcY := by
        funext n F
        exact PEmpty.elim F
      cases hr
      cases hf
      rfl

/-- The canonical functional presentation of a genuine relational
rectangle structure interprets the original structure LITERALLY,
not only up to an unspecified isomorphism. -/
theorem IsRectangleStructure.toRawPresentation_toStructure_eq
    (h : IsRectangleStructure d A) :
    h.toRawPresentation.toStructure = A := by
  apply rectangleStructure_eq_of_rel_iff
  intro n R xs
  rcases R with ⟨name, hn⟩
  subst n
  cases name with
  | none =>
      change partRel h.toRawPresentation.toStructure (xs 0) (xs 1) ↔
        partRel A (xs 0) (xs 1)
      exact h.rawPresentation_part_exact (xs 0) (xs 1)
  | some c =>
      change rawRel h.toRawPresentation.toStructure c (xs 0) (xs 1) ↔
        rawRel A c (xs 0) (xs 1)
      exact h.rawPresentation_colour_exact c (xs 0) (xs 1)

end SemigenericEPPA
