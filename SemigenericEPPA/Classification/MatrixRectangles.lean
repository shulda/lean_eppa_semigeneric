import SemigenericEPPA.Classification.RectangleDisplacements

/-!
# Tiny 2+2 raw rectangle matrices

The SAP-to-classification converse can be witnessed by finite two-part
matrices. This file verifies their elementary compatibility independently
of the general relational API. A literal relational matrix structure and
the two required SAP arguments will build on these facts.
-/

namespace SemigenericEPPA.Classification

universe u v w

namespace RectangleRule

variable {C : Type u} (R : RectangleRule C)
variable {X : Type v} {Y : Type w}

/-- Every ordered distinct row pair and ordered distinct column pair
of a raw matrix forms an allowed 2+2 rectangle. -/
def MatrixAdmissible (M : X → Y → C) : Prop :=
  ∀ x₀ x₁ y₀ y₁, x₀ ≠ x₁ → y₀ ≠ y₁ →
    R.allowed (M x₀ y₀) (M x₀ y₁) (M x₁ y₀) (M x₁ y₁)

/-- The same matrix read backwards has precisely the starred transpose
of the original rectangle, as demanded by raw edge reversal. -/
theorem matrixAdmissible_starredTranspose
    (M : X → Y → C) (h : R.MatrixAdmissible M)
    (x₀ x₁ : X) (y₀ y₁ : Y)
    (hx : x₀ ≠ x₁) (hy : y₀ ≠ y₁) :
    R.allowed
      (R.reverse (M x₀ y₀))
      (R.reverse (M x₁ y₀))
      (R.reverse (M x₀ y₁))
      (R.reverse (M x₁ y₁)) :=
  (R.starred_transpose
    (M x₀ y₀) (M x₀ y₁) (M x₁ y₀) (M x₁ y₁)).mp
    (h x₀ x₁ y₀ y₁ hx hy)

/-- A 2+2 matrix with its standard row and column ordering. -/
def squareMatrix (a b c d : C) : Bool → Bool → C
  | false, false => a
  | false, true => b
  | true, false => c
  | true, true => d

/-- A single P(a,b,c,d) checks all ordered row and column readings
of the 2+2 matrix, using only rectangle isomorphism symmetries. -/
theorem squareMatrix_admissible (a b c d : C)
    (h : R.allowed a b c d) :
    R.MatrixAdmissible (R.squareMatrix a b c d) := by
  have hcol : R.allowed b a d c := (R.col_swap a b c d).mp h
  have hrow : R.allowed c d a b := (R.row_swap a b c d).mp h
  have hboth : R.allowed d c b a :=
    (R.col_swap c d a b).mp hrow
  intro x₀ x₁ y₀ y₁ hx hy
  cases x₀ <;> cases x₁ <;> cases y₀ <;> cases y₁ <;>
    simp_all [squareMatrix]

/-- With a singleton row part, no genuine 2+2 rectangle exists. -/
theorem matrixAdmissible_subsingleton_rows
    [Subsingleton X] (M : X → Y → C) :
    R.MatrixAdmissible M := by
  intro x₀ x₁ y₀ y₁ hx _
  exact (hx (Subsingleton.elim x₀ x₁)).elim

/-- With a singleton column part, likewise. -/
theorem matrixAdmissible_subsingleton_columns
    [Subsingleton Y] (M : X → Y → C) :
    R.MatrixAdmissible M := by
  intro x₀ x₁ y₀ y₁ _ hy
  exact (hy (Subsingleton.elim y₀ y₁)).elim

end RectangleRule
end SemigenericEPPA.Classification
