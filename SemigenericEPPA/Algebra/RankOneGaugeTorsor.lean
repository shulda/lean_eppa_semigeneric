import SemigenericEPPA.Algebra.Rectangle
import Mathlib.Tactic.Group

/-!
# Unique transitions between noncommutative rank-one factors

When F(x,y) = row(x) * col(y) = row'(x) * col'(y),
one unique k ∈ G satisfies row'(x) = row(x) * k and
col'(y) = k⁻¹ * col(y). Noncommutative order is essential.

Nonempty row/column types are witnessed by anchors p and q.
This is the elementary torsor kernel for gauge presentations.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}

/-- Two rank-one presentations of the same matrix differ by one
right-row/left-column multiplier. -/
theorem rankOne_factor_transition
    (row row' : X → G) (col col' : Y → G)
    (h : ∀ x y, row x * col y = row' x * col' y)
    (p : X) (q : Y) :
    ∃ k : G,
      (∀ x, row' x = row x * k) ∧
      (∀ y, col' y = k⁻¹ * col y) := by
  let k : G := (row p)⁻¹ * row' p
  have hcol : ∀ y, col' y = k⁻¹ * col y := by
    intro y
    have hy := h p y
    calc
      col' y = (row' p)⁻¹ * (row' p * col' y) := by group
      _ = (row' p)⁻¹ * (row p * col y) := by rw [← hy]
      _ = k⁻¹ * col y := by dsimp [k]; group
  have hrow : ∀ x, row' x = row x * k := by
    intro x
    have hx := h x q
    calc
      row' x = (row' x * col' q) * (col' q)⁻¹ := by group
      _ = (row x * col q) * (col' q)⁻¹ := by rw [← hx]
      _ = row x * k := by rw [hcol q]; dsimp [k]; group
  exact ⟨k, hrow, hcol⟩

/-- The transition is already determined by a single old row anchor. -/
theorem rankOne_transition_unique
    (row row' : X → G) (p : X) (k l : G)
    (hk : ∀ x, row' x = row x * k)
    (hl : ∀ x, row' x = row x * l) :
    k = l := by
  calc
    k = (row p)⁻¹ * row' p := by rw [hk p]; group
    _ = l := by rw [hl p]; group

/-- Every such gauge change preserves the underlying matrix. -/
theorem rankOne_transition_preserves
    (row : X → G) (col : Y → G) (k : G) (x : X) (y : Y) :
    (row x * k) * (k⁻¹ * col y) = row x * col y := by
  group

/-- Existence AND uniqueness of the transition group element. -/
theorem rankOne_factor_transition_unique
    (row row' : X → G) (col col' : Y → G)
    (h : ∀ x y, row x * col y = row' x * col' y)
    (p : X) (q : Y) :
    ∃! k : G,
      (∀ x, row' x = row x * k) ∧
      (∀ y, col' y = k⁻¹ * col y) := by
  obtain ⟨k, hkrow, hkcol⟩ :=
    rankOne_factor_transition row row' col col' h p q
  refine ⟨k, ⟨hkrow, hkcol⟩, ?_⟩
  intro l hl
  exact rankOne_transition_unique row row' p l k hl.1 hkrow

end SemigenericEPPA
