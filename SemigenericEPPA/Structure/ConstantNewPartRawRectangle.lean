import SemigenericEPPA.Structure.RawPresentation

/-!
# A single new E-class with constant raw cross-colours

The realization of an abstract finite group cover in the original
R1–R3 rectangle class adds one new equivalence class R carrying
a regular group action. Every directed cross-pair from R to the
old structure has the same raw colour c0, with the reversed raw
colour on the reverse orientation. No extra rectangle condition
arises because effective rows to this new class are constant.

This module constructs the exact functional raw presentation on
the sum V⊕R and proves the complete original R1–R3 axioms,
preserving all old E and P_c predicates literally.

It does NOT yet install the group action or prove faithfulness;
those depend only on the chosen regular action and preservation
of the original old structure.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {R : Type t} {d : RawDatum G C}

/-- E is the old E on V and the universal relation on R;
the two summands are not E-related. -/
def constantNewPartRel
    (P : RawRectanglePresentation d V)
    (x y : V ⊕ R) : Prop :=
  match x, y with
  | .inl a, .inl b => P.part a b
  | .inr _, .inr _ => True
  | _, _ => False

/-- All old raw colours are untouched, while new-to-old
cross-pairs have colour c and the opposite direction reverse(c). -/
def constantNewPartColour
    (P : RawRectanglePresentation d V) (c : C)
    (x y : V ⊕ R) : Option C :=
  match x, y with
  | .inl a, .inl b => P.colour a b
  | .inr _, .inr _ => none
  | .inr _, .inl _ => some c
  | .inl _, .inr _ => some (d.reverse c)

/-- An entire new equivalence class of arbitrary size can be
adjoined with constant raw cross-colours, preserving the rectangle
equations for arbitrary nonabelian G and affine reversal. -/
def RawRectanglePresentation.adjoinConstantNewPart
    (P : RawRectanglePresentation d V) (c : C) :
    RawRectanglePresentation d (V ⊕ R) where
  part := constantNewPartRel P
  part_equiv := by
    constructor
    · intro x
      cases x with
      | inl a => exact P.part_equiv.refl a
      | inr _ => trivial
    · intro x y h
      cases x <;> cases y <;>
        simp [constantNewPartRel] at h ⊢
      exact P.part_equiv.symm h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;>
        simp [constantNewPartRel] at hxy hyz ⊢
      exact P.part_equiv.trans hxy hyz
  colour := constantNewPartColour P c
  colour_none_iff := by
    intro x y
    cases x <;> cases y <;>
      simp [constantNewPartRel, constantNewPartColour,
        P.colour_none_iff]
  colour_reverse := by
    intro x y
    cases x with
    | inl a =>
        cases y with
        | inl b => exact P.colour_reverse a b
        | inr r => simp [constantNewPartColour, d.reverse_involutive]
    | inr r =>
        cases y with
        | inl a => rfl
        | inr r' => rfl
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11
    cases x₀ <;> cases x₁ <;> cases y₀ <;> cases y₁ <;>
      simp_all [constantNewPartRel, constantNewPartColour]
    exact P.rectangle _ _ _ _ hx hy _ _ _ _ h00 h01 h10 h11

/-- Old vertices retain their exact original E relation. -/
theorem RawRectanglePresentation.adjoinConstantNewPart_old_part
    (P : RawRectanglePresentation d V) (c : C) (x y : V) :
    (P.adjoinConstantNewPart (R := R) c).part
        (.inl x) (.inl y) ↔ P.part x y :=
  Iff.rfl

/-- Old directed raw colours are preserved literally. -/
theorem RawRectanglePresentation.adjoinConstantNewPart_old_colour
    (P : RawRectanglePresentation d V) (c : C) (x y : V) :
    (P.adjoinConstantNewPart (R := R) c).colour
        (.inl x) (.inl y) = P.colour x y := rfl

end SemigenericEPPA
