import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import Mathlib.Data.Fintype.Option

/-!
# A freely prescribed raw profile from a new singleton E-class

For a complete original-language R1--R3 rectangle presentation P
on V, choose ANY raw colours f(x) for ordered pairs from a new
vertex v to each old vertex x. Put v into its own singleton E-class,
retain every old raw colour literally, and use reverse(f(x)) in the
opposite direction. The result is again a rectangle presentation.

There is no rank-one compatibility condition on f: every 2-by-2
rectangle involving the new E-class repeats the only new vertex,
and therefore imposes the tautological equality of two identical
rows or columns. The old rectangles are exactly those of P.

This is the finite one-point raw construction used in negative DLF
delta-profile forcing and orbit-killer gadgets, not a completion of
an arbitrary partial old colouring.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

/-- E is unchanged on the old vertices, and the new none vertex
forms its own singleton equivalence class. -/
def singletonNewPartRel
    (P : RawRectanglePresentation d V) (x y : Option V) : Prop :=
  match x, y with
  | some a, some b => P.part a b
  | none, none => True
  | _, _ => False

/-- Every old raw colour is retained; new-to-old colours are
the arbitrary prescribed f(x), reversed in the other direction. -/
def singletonNewPartColour
    (P : RawRectanglePresentation d V) (f : V → C)
    (x y : Option V) : Option C :=
  match x, y with
  | some a, some b => P.colour a b
  | none, none => none
  | none, some b => some (f b)
  | some a, none => some (d.reverse (f a))

/-- Any raw profile f across a new singleton E-class produces a
genuine complete R1--R3 rectangle presentation. -/
def RawRectanglePresentation.adjoinSingletonPart
    (P : RawRectanglePresentation d V) (f : V → C) :
    RawRectanglePresentation d (Option V) where
  part := singletonNewPartRel P
  part_equiv := by
    constructor
    · intro x
      cases x with
      | none => trivial
      | some a => exact P.part_equiv.refl a
    · intro x y h
      cases x <;> cases y <;>
        simp [singletonNewPartRel] at h ⊢
      exact P.part_equiv.symm h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;>
        simp [singletonNewPartRel] at hxy hyz ⊢
      exact P.part_equiv.trans hxy hyz
  colour := singletonNewPartColour P f
  colour_none_iff := by
    intro x y
    cases x <;> cases y <;>
      simp [singletonNewPartRel, singletonNewPartColour,
        P.colour_none_iff]
  colour_reverse := by
    intro x y
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some b => rfl
    | some a =>
        cases y with
        | none => simp [singletonNewPartColour, d.reverse_involutive]
        | some b => exact P.colour_reverse a b
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11
    cases x₀ <;> cases x₁ <;> cases y₀ <;> cases y₁ <;>
      simp_all [singletonNewPartRel, singletonNewPartColour, inv_mul_cancel]
    exact P.rectangle _ _ _ _ hx hy _ _ _ _ h00 h01 h10 h11

/-- The whole original equivalence relation on old vertices is
preserved and reflected, with no additional identifications. -/
theorem RawRectanglePresentation.adjoinSingletonPart_oldPart
    (P : RawRectanglePresentation d V) (f : V → C)
    (x y : V) :
    (P.adjoinSingletonPart f).part (some x) (some y) ↔
      P.part x y :=
  Iff.rfl

/-- Every ordered old raw colour is preserved literally. -/
theorem RawRectanglePresentation.adjoinSingletonPart_oldColour
    (P : RawRectanglePresentation d V) (f : V → C)
    (x y : V) :
    (P.adjoinSingletonPart f).colour (some x) (some y) =
      P.colour x y := rfl

/-- The new vertex and each old vertex are in different E-classes. -/
theorem RawRectanglePresentation.adjoinSingletonPart_newCross
    (P : RawRectanglePresentation d V) (f : V → C)
    (x : V) : ¬(P.adjoinSingletonPart f).part none (some x) := by
  intro h
  cases h

/-- The actual effective colour on the new-to-old edge is
EXACTLY phi(f(x)), not merely congruent to it. -/
theorem RawRectanglePresentation.adjoinSingletonPart_effectiveColour
    (P : RawRectanglePresentation d V) (f : V → C)
    (x : V) :
    (P.adjoinSingletonPart f).effectiveReduct.F none (some x) =
      d.phi (f x) := by
  exact ((P.adjoinSingletonPart f).effectiveReduct_crossColour
    none (some x) (f x) rfl).symm

/-- A single new singleton E-class can realize the asymmetric
delta-profile (delta,1,1) towards any distinct a,b,c with
b ≠ a and c ≠ a. All old raw colours remain literally unchanged. -/
theorem RawRectanglePresentation.exists_singletonDeltaProfile
    (P : RawRectanglePresentation d V)
    (a b c : V)
    (hba : b ≠ a) (hca : c ≠ a)
    (delta : G) :
    ∃ f : V → C,
      (P.adjoinSingletonPart f).effectiveReduct.F none (some a) = delta ∧
      (P.adjoinSingletonPart f).effectiveReduct.F none (some b) = 1 ∧
      (P.adjoinSingletonPart f).effectiveReduct.F none (some c) = 1 := by
  classical
  obtain ⟨cdelta, hdelta⟩ := d.phi_surjective delta
  obtain ⟨cone, hone⟩ := d.phi_surjective 1
  let f : V → C := fun x => if x = a then cdelta else cone
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [P.adjoinSingletonPart_effectiveColour]
    simp [f, hdelta]
  · rw [P.adjoinSingletonPart_effectiveColour]
    simp [f, hba, hone]
  · rw [P.adjoinSingletonPart_effectiveColour]
    simp [f, hca, hone]

end SemigenericEPPA
