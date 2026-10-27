import SemigenericEPPA.Classification.GeneralRuleStructure
import SemigenericEPPA.Structure.RawPresentation
import Mathlib.Algebra.Group.PUnit

/-!
# Realization of raw two-part matrices in the literal E/R_c language

Every finite X-by-Y raw matrix is a genuine relational structure on
X ⊕ Y: the two summands are exactly its equivalence classes, and the
reverse edges carry reversal colours. The rectangle rule is imposed
only on distinct rows and columns.

The PUnit-valued RawRectanglePresentation below is merely a syntax
bridge for the relational language; no algebraic structure is imposed
on the general rectangle predicate.
-/

namespace SemigenericEPPA.Classification

open AllThoseEPPA

universe u

namespace RectangleRule

variable {C X Y : Type u} (R : RectangleRule C)

/-- The trivial effective datum is used ONLY to encode raw matrices
in the existing original-relational binary language. -/
noncomputable def syntaxDatum (c₀ : C) : RawDatum PUnit.{u} C where
  s := {
    toFun := id
    involutive := by intro x; rfl
    map_mul := by intro x y; exact Subsingleton.elim _ _ }
  reverse := R.reverse
  reverse_involutive := R.reverse_involutive
  phi := fun _ => 1
  phi_surjective := by
    intro g
    exact ⟨c₀, Subsingleton.elim _ _⟩
  equivariant := by intro _; rfl

/-- Exactly two E-classes, one for rows and the other for columns. -/
def matrixPart (v w : X ⊕ Y) : Prop :=
  match v, w with
  | .inl _, .inl _ => True
  | .inr _, .inr _ => True
  | _, _ => False

/-- Ordered raw colours from a matrix, with automatic reversal. -/
def matrixColour (M : X → Y → C) (v w : X ⊕ Y) : Option C :=
  match v, w with
  | .inl x, .inr y => some (M x y)
  | .inr y, .inl x => some (R.reverse (M x y))
  | _, _ => none

/-- Functional original-language realization: the dummy effective
group is PUnit, so its R3 law is automatically true. -/
noncomputable def matrixRaw (c₀ : C) (M : X → Y → C) :
    RawRectanglePresentation (R.syntaxDatum c₀) (X ⊕ Y) where
  part := matrixPart
  part_equiv := by
    constructor
    · intro v
      cases v <;> simp [matrixPart]
    · intro v w h
      cases v <;> cases w <;> simp_all [matrixPart]
    · intro v w z hvw hwz
      cases v <;> cases w <;> cases z <;>
        simp_all [matrixPart]
  colour := R.matrixColour M
  colour_none_iff := by
    intro v w
    cases v <;> cases w <;>
      simp [matrixColour, matrixPart]
  colour_reverse := by
    intro v w
    cases v <;> cases w <;>
      simp [matrixColour, syntaxDatum, R.reverse_involutive]
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy a b c d h00 h01 h10 h11
    exact Subsingleton.elim _ _

/-- An actual binary E/R_c structure for the raw matrix. -/
noncomputable def matrixStructure (c₀ : C) (M : X → Y → C) :
    Structure (rectangleLanguage C) (X ⊕ Y) :=
  (R.matrixRaw c₀ M).toStructure

@[simp] theorem matrixStructure_part (c₀ : C) (M : X → Y → C)
    (v w : X ⊕ Y) :
    partRel (R.matrixStructure c₀ M) v w ↔ matrixPart v w :=
  Iff.rfl

@[simp] theorem matrixStructure_colour (c₀ c : C)
    (M : X → Y → C) (v w : X ⊕ Y) :
    rawRel (R.matrixStructure c₀ M) c v w ↔
      R.matrixColour M v w = some c :=
  Iff.rfl

/-- The relational realization belongs to the completely unrestricted
P-rectangle age exactly when the matrix itself is admissible. -/
theorem matrixStructure_isRule (c₀ : C) (M : X → Y → C)
    (hM : R.MatrixAdmissible M) :
    IsRuleStructure R (R.matrixStructure c₀ M) := by
  let hTriv : IsRectangleStructure (R.syntaxDatum c₀)
      (R.matrixStructure c₀ M) :=
    (R.matrixRaw c₀ M).toStructure_isRectangleStructure
  refine {
    parts_equiv := hTriv.parts_equiv
    raw_only_cross := hTriv.raw_only_cross
    cross_unique := hTriv.cross_unique
    reverse := hTriv.reverse
    rectangle := ?_ }
  intro x₀ x₁ y₀ y₁ hxx hyy hx hy a b c d ha hb hc hd
  cases x₀ <;> cases x₁ <;> cases y₀ <;> cases y₁ <;>
    simp_all [matrixStructure_part, matrixStructure_colour,
      matrixPart, matrixColour]
  · simpa_all using hM _ _ _ _ (by simpa using hxx) (by simpa using hyy)
  · simpa_all using R.matrixAdmissible_starredTranspose M hM _ _ _ _
      (by simpa using hyy) (by simpa using hxx)

end RectangleRule

end SemigenericEPPA.Classification
