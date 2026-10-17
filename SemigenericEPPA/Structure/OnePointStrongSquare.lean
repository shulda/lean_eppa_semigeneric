import SemigenericEPPA.Structure.StrongSquare
import SemigenericEPPA.Structure.LiteralSAPEmbeddings

/-!
# One-point strong SAP as a jointly surjective exact square

The genuine literal one-point SAP theorem already gives typed
AllThoseEPPA.Structure.Embedding maps from both one-point sides.
Here we show that they form an exact StrongSquare, including the
coverage property: EVERY amalgam vertex lies in one of the sides.

Thus the input of the abstract StrongSquare.paste theorem is
realized by the actual semigeneric rectangle class. This is the
direct interface for finite SAP iteration by successive one-point
strong pushouts.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

namespace LiteralOnePointDiagram

variable (Q : LiteralOnePointDiagram d V)

/-- Every finite literal one-point R1–R3 diagram has a *jointly
surjective* strong-amalgamation square of genuine upstream embeddings.
The output carrier is precisely V ⊕ Bool, with no extra vertices. -/
theorem finite_onePoint_strong_square
    [Fintype V]
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ) :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier V),
      IsRectangleStructure d S ∧
      ∃ (f : Structure.Embedding act Q.left S)
        (g : Structure.Embedding act Q.right S),
        StrongSquare
          (fun a : V => (some a : Option V))
          (fun a : V => (some a : Option V))
          (fun x : Option V => f x)
          (fun y : Option V => g y) := by
  obtain ⟨S, hS, f, g, hf, hg, hinter⟩ :=
    Q.finite_onePoint_strong_amalgamation_embeddings act
  refine ⟨S, hS, f, g, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a
    calc
      f (some a) = firstOnePoint (some a) := hf (some a)
      _ = secondOnePoint (some a) := rfl
      _ = g (some a) := (hg (some a)).symm
  · intro x y
    exact hinter x y
  · intro w
    cases w with
    | inl a =>
      left
      exact ⟨some a, hf (some a)⟩
    | inr flag =>
      cases flag with
      | false =>
        left
        exact ⟨none, hf none⟩
      | true =>
        right
        exact ⟨none, hg none⟩

end LiteralOnePointDiagram
end SemigenericEPPA
