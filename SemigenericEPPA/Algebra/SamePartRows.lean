import SemigenericEPPA.Algebra.CornerAmalgamation

/-!
# Two new points joining the same existing E-part

When two new points lie in the same old E-class, their rows toward
another old E-class must agree in horizontal displacement.
Dually, when they lie in the same column class, their columns must
satisfy the common row displacement law.

We prove the stronger statement that adding both rows (or both
columns) simultaneously produces a rank-one matrix. This covers all
rectangles involving the two new vertices and any two old vertices
of an opposite part. No commutativity is assumed.

This is a separate local step in the one-point strong-amalgamation
argument; it is not a proof of full SAP.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}

/-- Adjoin two independent new rows to the same old matrix. -/
def appendTwoRows (F : X → Y → G)
    (r₁ r₂ : Y → G) : (X ⊕ Bool) → Y → G
  | Sum.inl x, y => F x y
  | Sum.inr false, y => r₁ y
  | Sum.inr true, y => r₂ y

/-- Adjoin two independent new columns to the same old matrix. -/
def appendTwoColumns (F : X → Y → G)
    (c₁ c₂ : X → G) : X → (Y ⊕ Bool) → G
  | x, Sum.inl y => F x y
  | x, Sum.inr false => c₁ x
  | x, Sum.inr true => c₂ x

/-- The two added rows are compatible with every old row and one another,
because they share the same column factor in a rank-one decomposition. -/
theorem appendTwoRows_rankOne
    (F : X → Y → G) (hF : RectangleLaw F)
    (r₁ r₂ : Y → G) (p : X) (q : Y)
    (h₁ : RowCompatible F r₁ p q)
    (h₂ : RowCompatible F r₂ p q) :
    IsRankOne (appendTwoRows F r₁ r₂) := by
  refine ⟨(fun x => match x with
      | Sum.inl a => F a q
      | Sum.inr false => r₁ q
      | Sum.inr true => r₂ q),
    (fun y => (F p q)⁻¹ * F p y), ?_⟩
  intro x y
  cases x with
  | inl a =>
    change F a y = F a q * ((F p q)⁻¹ * F p y)
    simpa only [mul_assoc] using factor_of_rectangle F hF p q a y
  | inr b =>
    cases b with
    | false =>
      change r₁ y = r₁ q * ((F p q)⁻¹ * F p y)
      exact rowCompatible_formula F r₁ p q h₁ y
    | true =>
      change r₂ y = r₂ q * ((F p q)⁻¹ * F p y)
      exact rowCompatible_formula F r₂ p q h₂ y

/-- All rectangles involving either new row are satisfied at once. -/
theorem appendTwoRows_rectangle
    (F : X → Y → G) (hF : RectangleLaw F)
    (r₁ r₂ : Y → G) (p : X) (q : Y)
    (h₁ : RowCompatible F r₁ p q)
    (h₂ : RowCompatible F r₂ p q) :
    RectangleLaw (appendTwoRows F r₁ r₂) :=
  rectangle_of_rankOne _
    (appendTwoRows_rankOne F hF r₁ r₂ p q h₁ h₂)

/-- The two new rows have equal horizontal displacements; this is
the remaining same-E-part rectangle case in one-point SAP. -/
theorem compatible_new_rows
    (F : X → Y → G) (hF : RectangleLaw F)
    (r₁ r₂ : Y → G) (p : X) (q : Y)
    (h₁ : RowCompatible F r₁ p q)
    (h₂ : RowCompatible F r₂ p q)
    (y z : Y) :
    (r₁ y)⁻¹ * r₁ z = (r₂ y)⁻¹ * r₂ z := by
  have hh := appendTwoRows_rectangle F hF r₁ r₂ p q h₁ h₂
    (Sum.inr false) (Sum.inr true) y z
  simpa only [appendTwoRows] using hh

/-- The two added columns have the shared left factor F(x,q).
Thus no new column/column rectangle can fail. -/
theorem appendTwoColumns_rankOne
    (F : X → Y → G) (hF : RectangleLaw F)
    (c₁ c₂ : X → G) (p : X) (q : Y)
    (h₁ : ColumnCompatible F c₁ p q)
    (h₂ : ColumnCompatible F c₂ p q) :
    IsRankOne (appendTwoColumns F c₁ c₂) := by
  refine ⟨(fun x => F x q),
    (fun y => match y with
      | Sum.inl b => (F p q)⁻¹ * F p b
      | Sum.inr false => (F p q)⁻¹ * c₁ p
      | Sum.inr true => (F p q)⁻¹ * c₂ p), ?_⟩
  intro x y
  cases y with
  | inl b =>
    change F x b = F x q * ((F p q)⁻¹ * F p b)
    simpa only [mul_assoc] using factor_of_rectangle F hF p q x b
  | inr b =>
    cases b with
    | false =>
      change c₁ x = F x q * ((F p q)⁻¹ * c₁ p)
      exact columnCompatible_formula F c₁ p q h₁ x
    | true =>
      change c₂ x = F x q * ((F p q)⁻¹ * c₂ p)
      exact columnCompatible_formula F c₂ p q h₂ x

/-- All rectangles involving either new column are satisfied. -/
theorem appendTwoColumns_rectangle
    (F : X → Y → G) (hF : RectangleLaw F)
    (c₁ c₂ : X → G) (p : X) (q : Y)
    (h₁ : ColumnCompatible F c₁ p q)
    (h₂ : ColumnCompatible F c₂ p q) :
    RectangleLaw (appendTwoColumns F c₁ c₂) :=
  rectangle_of_rankOne _
    (appendTwoColumns_rankOne F hF c₁ c₂ p q h₁ h₂)

/-- The two new columns have equal vertical cross-displacements,
in the noncommutative order required by the rectangle law. -/
theorem compatible_new_columns
    (F : X → Y → G) (hF : RectangleLaw F)
    (c₁ c₂ : X → G) (p : X) (q : Y)
    (h₁ : ColumnCompatible F c₁ p q)
    (h₂ : ColumnCompatible F c₂ p q)
    (x z : X) :
    (c₁ x)⁻¹ * c₂ x = (c₁ z)⁻¹ * c₂ z := by
  have hh := appendTwoColumns_rectangle F hF c₁ c₂ p q h₁ h₂
    x z (Sum.inr false) (Sum.inr true)
  simpa only [appendTwoColumns] using hh

end SemigenericEPPA
