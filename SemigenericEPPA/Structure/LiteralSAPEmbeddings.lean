import SemigenericEPPA.Structure.LiteralOnePointSAP
import SemigenericEPPA.Structure.PairwiseEmbedding

/-!
# One-point strong amalgamation with genuine upstream embeddings

The literal one-point SAP theorem previously returned a structure
and exact per-pair E/P_c equivalences. We package those exact
equivalences as actual AllThoseEPPA.Structure.Embedding maps with
identity language component.

The two embeddings overlap in exactly the original base vertices.
No extra identifications are allowed in the amalgam. This is the
categorical formulation required by finite SAP iteration and later
Fraïssé and EPPA arguments.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- The two canonical injections from an old carrier plus one new
point into an old carrier plus two new points meet precisely on
the old carrier. This is the *strong* rather than ordinary
amalgamation-overlap property. -/
theorem onePoint_embeddings_overlap (x y : Option V) :
    firstOnePoint x = secondOnePoint y ↔
      ∃ a : V, x = some a ∧ y = some a := by
  cases x with
  | none =>
    cases y with
    | none =>
      simp [firstOnePoint, secondOnePoint]
    | some b =>
      simp [firstOnePoint, secondOnePoint]
  | some a =>
    cases y with
    | none =>
      simp [firstOnePoint, secondOnePoint]
    | some b =>
      constructor
      · intro h
        have hab : a = b := Sum.inl.inj h
        subst b
        exact ⟨a, rfl, rfl⟩
      · rintro ⟨c, hc, hc'⟩
        have hac : a = c := Option.some.inj hc
        have hbc : b = c := Option.some.inj hc'
        change (Sum.inl a : TwoPointCarrier V) = Sum.inl b
        rw [hac, hbc]

namespace LiteralOnePointDiagram

variable (Q : LiteralOnePointDiagram d V)

/-- Exact finite one-point strong amalgamation as a diagram of two
*real* AllThoseEPPA.Structure.Embedding maps. The embeddings have
identity language components, agree on all old vertices, reflect all
raw predicates, and overlap only on the old base.

This strengthens the verified relation-wise SAP theorem without
changing its hypotheses or introducing any additional mathematical
existence argument. -/
theorem finite_onePoint_strong_amalgamation_embeddings
    [Fintype V]
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ) :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier V),
      IsRectangleStructure d S ∧
      ∃ (f : Structure.Embedding act Q.left S)
        (g : Structure.Embedding act Q.right S),
        (∀ x : Option V, f x = firstOnePoint x) ∧
        (∀ y : Option V, g y = secondOnePoint y) ∧
        (∀ x y : Option V,
          f x = g y ↔ ∃ a : V, x = some a ∧ y = some a) := by
  obtain ⟨S, hS, hLpart, hRpart, hLraw, hRraw⟩ :=
    Q.finite_onePoint_strong_amalgamation
  let f : Structure.Embedding act Q.left S :=
    embeddingOfPairwiseEquiv act Q.left S
      firstOnePoint firstOnePoint_injective
      hLpart hLraw
  let g : Structure.Embedding act Q.right S :=
    embeddingOfPairwiseEquiv act Q.right S
      secondOnePoint secondOnePoint_injective
      hRpart hRraw
  refine ⟨S, hS, f, g, (fun _ => rfl), (fun _ => rfl), ?_⟩
  intro x y
  exact onePoint_embeddings_overlap x y

end LiteralOnePointDiagram
end SemigenericEPPA
