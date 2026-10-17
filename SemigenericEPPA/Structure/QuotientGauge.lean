import SemigenericEPPA.Structure.EffectiveGeometry
import SemigenericEPPA.Algebra.Gauge

/-!
# Canonical two-sorted gauge presentations

This is the constructive forward direction of equation (2.6) in
the manuscript. The imaginary sort is the actual quotient V/E.
Skeleton colours K_ij satisfy K_ji = s(K_ij) for distinct parts,
while λ_(x,j) is a vertex-to-imaginary gauge coordinate.

The formula
    F(x,y) = s(λ_(x,[y])) K_[x],[y]⁻¹ λ_(y,[x])
defines an effective rectangle geometry for EVERY such gauge datum.
No finiteness, commutativity, or chosen ordering is used. The
value inside E-classes is an irrelevant dummy, not a colour.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Gauge data on the canonical E-quotient imaginary sort. -/
structure QuotientGauge (s : AffineAntiInvolution G) (V : Type v) where
  part : Setoid V
  skeleton : Quotient part → Quotient part → G
  skeleton_reverse :
    ∀ i j : Quotient part, i ≠ j →
      skeleton j i = s (skeleton i j)
  vertexGauge : V → Quotient part → G

namespace QuotientGauge

variable (P : QuotientGauge s V)

def cls (x : V) : Quotient P.part :=
  Quotient.mk P.part x

theorem cls_eq_iff (x y : V) :
    P.cls x = P.cls y ↔ P.part x y :=
  ⟨Quotient.exact, Quotient.sound⟩

noncomputable def effective (x y : V) : G := by
  classical
  exact if P.part x y then 1
    else gaugeColour s
      (P.vertexGauge x (P.cls y))
      (P.skeleton (P.cls x) (P.cls y))
      (P.vertexGauge y (P.cls x))

theorem effective_cross (x y : V) (hxy : ¬P.part x y) :
    P.effective x y =
      gaugeColour s
        (P.vertexGauge x (P.cls y))
        (P.skeleton (P.cls x) (P.cls y))
        (P.vertexGauge y (P.cls x)) := by
  simp [effective, hxy]

theorem effective_reverse (x y : V) (hxy : ¬P.part x y) :
    P.effective y x = s (P.effective x y) := by
  have hyx : ¬P.part y x := by
    intro h
    exact hxy (P.part.iseqv.symm h)
  rw [P.effective_cross y x hyx, P.effective_cross x y hxy]
  have hdistinct : P.cls x ≠ P.cls y := by
    intro h
    exact hxy ((P.cls_eq_iff x y).mp h)
  rw [P.skeleton_reverse (P.cls x) (P.cls y) hdistinct]
  exact (gauge_reverse s
    (P.vertexGauge x (P.cls y))
    (P.skeleton (P.cls x) (P.cls y))
    (P.vertexGauge y (P.cls x))).symm

/-- Every rectangle is rank-one on its two E-parts. -/
theorem effective_rectangle
    (x₀ x₁ y₀ y₁ : V)
    (hx : P.part x₀ x₁)
    (hy : P.part y₀ y₁)
    (h00 : ¬P.part x₀ y₀) :
    (P.effective x₀ y₀)⁻¹ * P.effective x₀ y₁ =
      (P.effective x₁ y₀)⁻¹ * P.effective x₁ y₁ := by
  have h01 : ¬P.part x₀ y₁ := by
    intro h
    exact h00 (P.part.iseqv.trans h (P.part.iseqv.symm hy))
  have h10 : ¬P.part x₁ y₀ := by
    intro h
    exact h00 (P.part.iseqv.trans hx h)
  have h11 : ¬P.part x₁ y₁ := by
    intro h
    exact h00 (P.part.iseqv.trans hx
      (P.part.iseqv.trans h (P.part.iseqv.symm hy)))
  have hix : P.cls x₁ = P.cls x₀ :=
    (P.cls_eq_iff x₁ x₀).2 (P.part.iseqv.symm hx)
  have hiy : P.cls y₁ = P.cls y₀ :=
    (P.cls_eq_iff y₁ y₀).2 (P.part.iseqv.symm hy)
  have hr := gauge_rectangle s
    (P.skeleton (P.cls x₀) (P.cls y₀))
    (fun x => P.vertexGauge x (P.cls y₀))
    (fun y => P.vertexGauge y (P.cls x₀))
    x₀ x₁ y₀ y₁
  rw [P.effective_cross x₀ y₀ h00,
    P.effective_cross x₀ y₁ h01,
    P.effective_cross x₁ y₀ h10,
    P.effective_cross x₁ y₁ h11]
  simp only [hix, hiy]
  exact hr

/-- Every canonical quotient-gauge system gives a genuine effective
E-rectangle geometry, including affine reversal. -/
noncomputable def toEffectiveGeometry : EffectiveGeometry s V where
  part := P.part
  F := P.effective
  reverse_cross := P.effective_reverse
  rectangle := P.effective_rectangle

theorem toEffectiveGeometry_part (x y : V) :
    P.toEffectiveGeometry.part x y ↔ P.part x y :=
  Iff.rfl

end QuotientGauge
end SemigenericEPPA
