import Mathlib.Tactic.Group

/-!
# Noncommutative rank-one rectangle law

A complete effective cross-part matrix takes values in an arbitrary group G,
not necessarily abelian. The rectangle law is exactly rank-one factorization
in the order F(x,y) = u(x) * v(y).

The statements are independent of finiteness and of selected part indices.
For a pair of nonempty parts, choose their anchors p and q.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}

/-- Equal horizontal displacements along every two-row, two-column rectangle. -/
def RectangleLaw (F : X → Y → G) : Prop :=
  ∀ x₀ x₁ y₀ y₁,
    (F x₀ y₀)⁻¹ * F x₀ y₁ = (F x₁ y₀)⁻¹ * F x₁ y₁

/-- Noncommutative rank-one factorization, with row factors on the left. -/
def IsRankOne (F : X → Y → G) : Prop :=
  ∃ (row : X → G) (col : Y → G), ∀ x y, F x y = row x * col y

/-- The manuscript's factorization at anchors p,q, without commutativity. -/
theorem factor_of_rectangle (F : X → Y → G)
    (h : RectangleLaw F) (p : X) (q : Y) (x : X) (y : Y) :
    F x y = F x q * (F p q)⁻¹ * F p y := by
  have hr := h p x q y
  calc
    F x y = F x q * ((F x q)⁻¹ * F x y) := by group
    _ = F x q * ((F p q)⁻¹ * F p y) := by rw [← hr]
    _ = F x q * (F p q)⁻¹ * F p y := by group

theorem rankOne_of_rectangle (F : X → Y → G)
    (h : RectangleLaw F) (p : X) (q : Y) :
    IsRankOne F := by
  refine ⟨(fun x => F x q), (fun y => (F p q)⁻¹ * F p y), ?_⟩
  intro x y
  simpa only [mul_assoc] using factor_of_rectangle F h p q x y

theorem rectangle_of_rankOne (F : X → Y → G)
    (h : IsRankOne F) : RectangleLaw F := by
  obtain ⟨row, col, hf⟩ := h
  intro x₀ x₁ y₀ y₁
  rw [hf x₀ y₀, hf x₀ y₁, hf x₁ y₀, hf x₁ y₁]
  group

/-- Exact equivalence for two anchored, nonempty parts. -/
theorem rectangle_iff_rankOne (F : X → Y → G)
    (p : X) (q : Y) :
    RectangleLaw F ↔ IsRankOne F :=
  ⟨fun h => rankOne_of_rectangle F h p q, rectangle_of_rankOne F⟩

end SemigenericEPPA
