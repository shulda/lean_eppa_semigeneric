import SemigenericEPPA.Algebra.GaugeConverse
import Mathlib.Tactic.Group

/-!
# The old two-part partial-isomorphism multiplier identities (3.14)--(3.15)

Whenever a nonempty bipartite submatrix has two presentations
with equal effective colours, choose one old vertex in each part.
The unique left multipliers are literally

  u = a'(x₀) * a(x₀)⁻¹,     v = b'(y₀) * b(y₀)⁻¹,

and they satisfy both coordinate equations (3.14) and the exact
noncommutative affine skeleton constraint (3.15):

  s.normalized(u) * (K')⁻¹ * v = K⁻¹.

Unlike an existence-only gauge change, this anchored version supplies
the concrete prescribed multiplier values for the E0 completion.
The later typed partial-isomorphism theorem must instantiate this
lemma on the intersections of a partial domain with two E-classes.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}

/-- Explicit anchored multipliers for two presentations of an old
cross-part matrix with exactly the same effective colours.
Noncommutative multiplication order is retained literally. -/
theorem anchored_partial_gauge_multipliers
    (s : AffineAntiInvolution G)
    (left left' : X → G)
    (right right' : Y → G)
    (K K' : G)
    (h : ∀ x y,
      gaugeColour s (left x) K (right y) =
        gaugeColour s (left' x) K' (right' y))
    (x₀ : X) (y₀ : Y) :
    let u := left' x₀ * (left x₀)⁻¹
    let v := right' y₀ * (right y₀)⁻¹
    (∀ x, left' x = u * left x) ∧
      (∀ y, right' y = v * right y) ∧
      s.normalized u * (K')⁻¹ * v = K⁻¹ := by
  obtain ⟨u, v, hu, hv, hK⟩ :=
    gauge_change_converse s left left' right right' K K' h x₀ y₀
  have hu₀ : left' x₀ * (left x₀)⁻¹ = u := by
    rw [hu x₀]
    group
  have hv₀ : right' y₀ * (right y₀)⁻¹ = v := by
    rw [hv y₀]
    group
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [hu₀]
    exact hu x
  · intro y
    rw [hv₀]
    exact hv y
  · rw [hu₀, hv₀, hK]
    dsimp [AffineAntiInvolution.normalized]
    group

end SemigenericEPPA
