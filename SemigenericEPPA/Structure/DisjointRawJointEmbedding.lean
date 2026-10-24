import SemigenericEPPA.Structure.RawPresentation

/-!
# Exact original-language joint embedding via disjoint union

The finite R1–R3 rectangle class has the joint embedding property
without any good-colour, congruence saturation or SAP assumption.

For two raw rectangle presentations P on V and Q on W, take the
disjoint union V ⊕ W. E remains the original relation within each
summand, and no E class crosses between them. Choose ANY raw colour
c for edges V→W, and its required reversal for W→V.

In the rectangle equation, each E-related pair lies entirely in
one summand. The four cross edges between different summands are
literally constant, so both sides of the noncommutative rectangle
identity coincide. All other rectangles are inherited from P or Q.

This produces a finite original-language JEP when the two input
carriers are finite. It is independent of strong amalgamation.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {W : Type t} {d : RawDatum G C}

/-- E on the disjoint union, with NO new identifications between
classes from the two input presentations. -/
def disjointJointPart (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (x y : V ⊕ W) : Prop :=
  match x, y with
  | .inl a, .inl b => P.part a b
  | .inr a, .inr b => Q.part a b
  | _, _ => False

/-- Ordered original raw colours: old predicates stay literal,
and both directions of a cross-summand pair are constant. -/
def disjointJointColour (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (c : C)
    (x y : V ⊕ W) : Option C :=
  match x, y with
  | .inl a, .inl b => P.colour a b
  | .inr a, .inr b => Q.colour a b
  | .inl _, .inr _ => some c
  | .inr _, .inl _ => some (d.reverse c)

namespace RawRectanglePresentation

/-- The disjoint union of TWO arbitrary original raw rectangles is
again a genuine R1–R3 rectangle, for an arbitrary chosen connecting
raw colour c, even for noncommutative G and general affine s. -/
def disjointJoint
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (c : C) :
    RawRectanglePresentation d (V ⊕ W) where
  part := disjointJointPart P Q
  part_equiv := by
    constructor
    · intro x
      cases x with
      | inl a => exact P.part_equiv.refl a
      | inr b => exact Q.part_equiv.refl b
    · intro x y h
      cases x <;> cases y <;>
        simp [disjointJointPart] at h ⊢
      · exact P.part_equiv.symm h
      · exact Q.part_equiv.symm h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;>
        simp [disjointJointPart] at hxy hyz ⊢
      · exact P.part_equiv.trans hxy hyz
      · exact Q.part_equiv.trans hxy hyz
  colour := disjointJointColour P Q c
  colour_none_iff := by
    intro x y
    cases x <;> cases y <;>
      simp [disjointJointPart, disjointJointColour,
        P.colour_none_iff, Q.colour_none_iff]
  colour_reverse := by
    intro x y
    cases x with
    | inl a =>
        cases y with
        | inl b => exact P.colour_reverse a b
        | inr b => rfl
    | inr a =>
        cases y with
        | inl b =>
            simp [disjointJointColour, d.reverse_involutive]
        | inr b => exact Q.colour_reverse a b
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    cases x₀ <;> cases x₁ <;> cases y₀ <;> cases y₁ <;>
      simp_all [disjointJointPart, disjointJointColour]
    · exact P.rectangle _ _ _ _ hx hy _ _ _ _ h00 h01 h10 h11
    · exact Q.rectangle _ _ _ _ hx hy _ _ _ _ h00 h01 h10 h11

/-- Literal E-preservation and reflection on the left summand. -/
@[simp] theorem disjointJoint_inl_part
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (c : C) (x y : V) :
    (P.disjointJoint Q c).part (.inl x) (.inl y) ↔
      P.part x y := Iff.rfl

/-- Literal E-preservation and reflection on the right summand. -/
@[simp] theorem disjointJoint_inr_part
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (c : C) (x y : W) :
    (P.disjointJoint Q c).part (.inr x) (.inr y) ↔
      Q.part x y := Iff.rfl

/-- Exact preservation of all ordered original R_c colours on V. -/
@[simp] theorem disjointJoint_inl_colour
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (c : C) (x y : V) :
    (P.disjointJoint Q c).colour (.inl x) (.inl y) =
      P.colour x y := rfl

/-- Exact preservation of all ordered original R_c colours on W. -/
@[simp] theorem disjointJoint_inr_colour
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) (c : C) (x y : W) :
    (P.disjointJoint Q c).colour (.inr x) (.inr y) =
      Q.colour x y := rfl

/-- An unconditionally available original-language JEP witness
for any two raw rectangles: surjectivity of phi supplies a raw
connecting colour over 1∈G, although ANY colour works. -/
theorem exists_disjointJoint
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W) :
    ∃ R : RawRectanglePresentation d (V ⊕ W),
      (∀ x y : V,
        R.part (.inl x) (.inl y) ↔ P.part x y) ∧
      (∀ x y : W,
        R.part (.inr x) (.inr y) ↔ Q.part x y) ∧
      (∀ x y : V,
        R.colour (.inl x) (.inl y) = P.colour x y) ∧
      (∀ x y : W,
        R.colour (.inr x) (.inr y) = Q.colour x y) := by
  let c : C := Classical.choose (d.phi_surjective 1)
  refine ⟨P.disjointJoint Q c, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact Iff.rfl
  · intro x y
    exact Iff.rfl
  · intro x y
    rfl
  · intro x y
    rfl

end RawRectanglePresentation
end SemigenericEPPA
