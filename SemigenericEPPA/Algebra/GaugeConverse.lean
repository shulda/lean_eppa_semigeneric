import SemigenericEPPA.Algebra.Gauge
import SemigenericEPPA.Algebra.RankOneGaugeTorsor

/-!
# Converse to the two-sorted affine gauge-change formula

For two presentations of one group-valued rectangle matrix
    F(x,y) = s(left(x)) K⁻¹ right(y),
the source paper's gauge-change formula is not only sufficient
(verified in Algebra/Gauge.lean), but NECESSARY:

  left'(x) = u * left(x),
  right'(y) = v * right(y),
  K' = v * K * s(1)⁻¹ * s(u).

The existence theorem works for any affine anti-involution and arbitrary
nonabelian group, with anchors certifying the two parts are nonempty.
The multipliers u,v are unique. This is the elementary two-part
gauge-torsor transition needed when aligning overlapping presentations.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}

/-- Any two affine gauge presentations of the same matrix are related
by the exact group multipliers prescribed in manuscript (2.7). -/
theorem gauge_change_converse
    (s : AffineAntiInvolution G)
    (left left' : X → G) (right right' : Y → G)
    (K K' : G)
    (h : ∀ x y,
      gaugeColour s (left x) K (right y) =
        gaugeColour s (left' x) K' (right' y))
    (p : X) (q : Y) :
    ∃ u v : G,
      (∀ x, left' x = u * left x) ∧
      (∀ y, right' y = v * right y) ∧
      K' = v * K * (s 1)⁻¹ * s u := by
  have hfact :
      ∀ x y,
        s (left x) * (K⁻¹ * right y) =
          s (left' x) * ((K')⁻¹ * right' y) := by
    intro x y
    simpa only [gaugeColour, mul_assoc] using h x y
  obtain ⟨k, hrow, hcol⟩ :=
    rankOne_factor_transition
      (fun x => s (left x))
      (fun x => s (left' x))
      (fun y => K⁻¹ * right y)
      (fun y => (K')⁻¹ * right' y) hfact p q
  let u : G := s (s 1 * k)
  have hk : (s 1)⁻¹ * s u = k := by
    dsimp [u]
    rw [s.involutive]
    group
  have hu : ∀ x, left' x = u * left x := by
    intro x
    apply s.injective
    calc
      s (left' x) = s (left x) * k := hrow x
      _ = s (left x) * ((s 1)⁻¹ * s u) := by rw [hk]
      _ = s (u * left x) := by rw [s.map_mul]; group
  let v : G := K' * k⁻¹ * K⁻¹
  have hv : ∀ y, right' y = v * right y := by
    intro y
    calc
      right' y = K' * ((K')⁻¹ * right' y) := by group
      _ = K' * (k⁻¹ * (K⁻¹ * right y)) := by rw [hcol y]
      _ = v * right y := by dsimp [v]; group
  have hK : K' = v * K * (s 1)⁻¹ * s u := by
    calc
      K' = K' * (k⁻¹ * k) := by group
      _ = (K' * k⁻¹ * K⁻¹) * K * ((s 1)⁻¹ * s u) := by
        rw [hk]
        group
      _ = v * K * (s 1)⁻¹ * s u := by dsimp [v]; group
  exact ⟨u, v, hu, hv, hK⟩

/-- Each multiplier is uniquely determined by the values at one
vertex in the corresponding part. -/
theorem gauge_transition_unique
    (left left' : X → G) (right right' : Y → G)
    (p : X) (q : Y)
    (u v u' v' : G)
    (hu : ∀ x, left' x = u * left x)
    (hv : ∀ y, right' y = v * right y)
    (hu' : ∀ x, left' x = u' * left x)
    (hv' : ∀ y, right' y = v' * right y) :
    u = u' ∧ v = v' := by
  constructor
  · calc
      u = left' p * (left p)⁻¹ := by rw [hu p]; group
      _ = u' := by rw [hu' p]; group
  · calc
      v = right' q * (right q)⁻¹ := by rw [hv q]; group
      _ = v' := by rw [hv' q]; group

/-- Exact equivalence of affine gauge colour equality and the
existence of manuscript multipliers u,v. -/
theorem gauge_equal_iff_transition
    (s : AffineAntiInvolution G)
    (left left' : X → G) (right right' : Y → G)
    (K K' : G) (p : X) (q : Y) :
    (∀ x y,
      gaugeColour s (left x) K (right y) =
        gaugeColour s (left' x) K' (right' y)) ↔
    ∃ u v : G,
      (∀ x, left' x = u * left x) ∧
      (∀ y, right' y = v * right y) ∧
      K' = v * K * (s 1)⁻¹ * s u := by
  constructor
  · intro h
    exact gauge_change_converse s left left' right right' K K' h p q
  · rintro ⟨u, v, hu, hv, hK⟩ x y
    rw [hu x, hv y, hK]
    exact (gauge_change s u v K (left x) (right y)).symm

end SemigenericEPPA
