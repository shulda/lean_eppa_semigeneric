import SemigenericEPPA.Bridge.BoundedPartsCoherentEPPA
import Mathlib.Algebra.Group.PUnit

/-!
# The two-orientation G=1 datum for n-partite tournaments

This file specializes the certified n-bounded coherent-EPPA result
to two opposite orientation symbols, and proves that the equivalence
relation E is *definable* from the single directed-edge relation by
mutual nonadjacency (including equality).

It deliberately distinguishes the original semigeneric E/R_false/R_true
language from the reduct with only a directed edge. An explicit
coherent-extension transport into the latter pure tournament language
requires an additional partial-automorphism/CoherentTriple bridge.
-/

namespace SemigenericEPPA

open AllThoseEPPA

/-- The canonical two raw orientations, reversed by Boolean negation,
with the unique effective group colour. Every rectangle is admitted. -/
noncomputable def twoOrientationGOneDatum : RawDatum PUnit Bool where
  s := {
    toFun := id
    involutive := by intro x; rfl
    map_mul := by intro x y; exact Subsingleton.elim _ _ }
  reverse := Bool.not
  reverse_involutive := by intro c; cases c <;> rfl
  phi := fun _ => 1
  phi_surjective := by
    intro g
    exact ⟨false, Subsingleton.elim _ _⟩
  equivariant := by intro c; exact Subsingleton.elim _ _

/-- The directed-edge predicate in the two-colour original relational
presentation: true indicates an arrow from x to y. -/
def orientedEdge {V : Type*}
    (A : Structure (rectangleLanguage Bool) V) (x y : V) : Prop :=
  rawRel A true x y

/-- For the two opposite raw orientation colours, the distinguished
equivalence relation is definable by nonadjacency, with no external
independent-part relation needed. -/
theorem twoOrientation_part_iff_nonadjacent
    {V : Type*}
    {A : Structure (rectangleLanguage Bool) V}
    (h : IsRectangleStructure twoOrientationGOneDatum A)
    (x y : V) :
    partRel A x y ↔
      ¬ orientedEdge A x y ∧ ¬ orientedEdge A y x := by
  constructor
  · intro hp
    constructor
    · intro hxy
      exact h.raw_only_cross true x y hxy hp
    · intro hyx
      exact h.raw_only_cross true y x hyx (h.parts_equiv.symm hp)
  · rintro ⟨hxy, hyx⟩
    by_contra hpart
    obtain ⟨c, hc, _⟩ := h.cross_unique x y hpart
    cases c with
    | false =>
        have hr : orientedEdge A y x := by
          have hr' := (h.reverse false x y).mp hc
          simpa [orientedEdge, twoOrientationGOneDatum] using hr'
        exact hyx hr
    | true =>
        exact hxy hc

/-- The fixed-n subclass corollary in the *expanded* original E/R_c
language, for the concrete two-orientation G=1 datum. Part count is
bounded by n, with unused part labels allowed (n=2,3,... in HJKS).
The pure single-edge language reduct is a distinct transport obligation. -/
theorem finite_twoOrientationExpandedNPartiteCoherentEPPA
    (n : ℕ) {V : Type*} [Finite V]
    {A : Structure (rectangleLanguage Bool) V}
    (h : IsRectangleStructure twoOrientationGOneDatum A)
    (hN : h.HasAtMostNonemptyParts n) :
    Finite h.finiteRelationalCoherentCarrier ∧
    ∃ (Q : RawRectanglePresentation twoOrientationGOneDatum
        h.finiteRelationalCoherentCarrier)
      (psiTyped : Structure.Embedding
        (rectangleTrivialAction Bool) A Q.toStructure),
      Structure.IsCoherentEPPAWitness
        (rectangleTrivialAction Bool) psiTyped ∧
      Q.toStructure_isRectangleStructure.HasAtMostNonemptyParts n ∧
      ∃ partEquiv :
          PartQuotient h ≃ PartQuotient Q.toStructure_isRectangleStructure,
        ∀ x : V,
          partEquiv (partClass h x) =
            partClass Q.toStructure_isRectangleStructure (psiTyped x) :=
  h.finite_boundedPartsRelationalCoherentEPPA_witness n hN

end SemigenericEPPA
