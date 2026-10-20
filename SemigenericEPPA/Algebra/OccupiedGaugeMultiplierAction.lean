import SemigenericEPPA.Algebra.AnchoredPartialGauge
import SemigenericEPPA.Algebra.OccupiedGaugeMultiplierExistence
import SemigenericEPPA.Algebra.EffectiveGroupGaugeCocycles
import Mathlib.Tactic.Group

/-!
# Canonical H-family of occupied gauge multipliers, including the skeleton

For an actual H-action rho on old vertices and iota on their
E-class indices, preserving the full noncommutative effective
cross-colour matrix, an occupied old class i has a real anchor x_i.

For every group element h and ordered pair (i,j), choose
  m_h(i,j) = a(h x_i, h j) * a(x_i,j)^-1
if i is occupied (and 1 otherwise). This family is fixed by the
ORIGINAL old action, not independently selected at each h.

For every DISTINCT OCCUPIED pair i,j:
* the SAME m_h(i,j) transports a(x,j) for ALL old x in class i;
* its reverse m_h(j,i) simultaneously transports the other row;
* both satisfy the literal affine/noncommutative skeleton equation
  normalized_s(m_h(i,j)) * K(h i,h j)^-1 * m_h(j,i)
    = K(i,j)^-1.

This is the first group-equivariant bridge from the individual
rank-one gauge transition (#249 / anchored (3.14)-(3.15)) to the
positive nontrivial-G coherent construction. It does not assert
an H-action on the full finite witness or handle unoccupied-pair
skeleton choices; the strict multiplier cocycle is the next gate.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {I : Type t}

/-- One fixed explicit multiplier for each h and ordered E-class
pair, anchored at a real old vertex of the source class whenever
that source class is occupied. No multiplier depends on a later
witness vertex or on an independently chosen automorphism lift. -/
noncomputable def occupiedGaugeActionMultiplier
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (h : H) (i j : I) : G := by
  classical
  exact if hi : ∃ x : V, cls x = i then
      a (rho h (Classical.choose hi)) (iota h j) *
        (a (Classical.choose hi) j)⁻¹
    else 1

/-- The multiplier formula at ANY fixed old source-class anchor. -/
theorem occupiedGaugeActionMultiplier_anchor
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (h : H) (i j : I)
    (hi : ∃ x : V, cls x = i) :
    occupiedGaugeActionMultiplier rho iota cls a h i j =
      a (rho h (Classical.choose hi)) (iota h j) *
        (a (Classical.choose hi) j)⁻¹ := by
  classical
  simp [occupiedGaugeActionMultiplier, hi]

/-- The multiplier is the identity at h=1 on EVERY source index,
including all unused indices (where it is defined to be 1). -/
theorem occupiedGaugeActionMultiplier_one
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (i j : I) :
    occupiedGaugeActionMultiplier rho iota cls a 1 i j = 1 := by
  classical
  by_cases hi : ∃ x : V, cls x = i
  · rw [occupiedGaugeActionMultiplier_anchor rho iota cls a 1 i j hi]
    simp
  · simp [occupiedGaugeActionMultiplier, hi]

/-- Exact old-coordinate transport AND the affine skeleton equation
on every pair of distinct, inhabited old E-classes. Works for any
affine reversal, including s(1)≠1, and arbitrary nonabelian G. -/
theorem occupiedGaugeActionMultiplier_preserves_old_pair
    (s : AffineAntiInvolution G)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (K : I → I → G)
    (hMatrix : ∀ (h : H) (x y : V),
      cls x ≠ cls y →
      gaugeColour s (a x (cls y))
        (K (cls x) (cls y)) (a y (cls x)) =
      gaugeColour s
        (a (rho h x) (iota h (cls y)))
        (K (iota h (cls x)) (iota h (cls y)))
        (a (rho h y) (iota h (cls x))))
    (h : H) (i j : I)
    (hi : ∃ x : V, cls x = i)
    (hj : ∃ y : V, cls y = j)
    (hij : i ≠ j) :
    (∀ x : V, cls x = i →
      a (rho h x) (iota h j) =
        occupiedGaugeActionMultiplier rho iota cls a h i j * a x j) ∧
    (∀ y : V, cls y = j →
      a (rho h y) (iota h i) =
        occupiedGaugeActionMultiplier rho iota cls a h j i * a y i) ∧
    s.normalized (occupiedGaugeActionMultiplier rho iota cls a h i j) *
        (K (iota h i) (iota h j))⁻¹ *
          occupiedGaugeActionMultiplier rho iota cls a h j i =
            (K i j)⁻¹ := by
  classical
  let X := {x : V // cls x = i}
  let Y := {y : V // cls y = j}
  let x0 : X := ⟨Classical.choose hi, Classical.choose_spec hi⟩
  let y0 : Y := ⟨Classical.choose hj, Classical.choose_spec hj⟩
  let left : X → G := fun x => a x.val j
  let left' : X → G := fun x => a (rho h x.val) (iota h j)
  let right : Y → G := fun y => a y.val i
  let right' : Y → G := fun y => a (rho h y.val) (iota h i)
  have hRows : ∀ x : X, ∀ y : Y,
      gaugeColour s (left x) (K i j) (right y) =
        gaugeColour s (left' x)
          (K (iota h i) (iota h j)) (right' y) := by
    intro x y
    have hxy : cls x.val ≠ cls y.val := by
      rw [x.property, y.property]
      exact hij
    simpa only [left, left', right, right', x.property, y.property] using
      hMatrix h x.val y.val hxy
  obtain ⟨hleft, hright, hskeleton⟩ :=
    anchored_partial_gauge_multipliers s
      left left' right right' (K i j)
      (K (iota h i) (iota h j)) hRows x0 y0
  have hmI :
      occupiedGaugeActionMultiplier rho iota cls a h i j =
        left' x0 * (left x0)⁻¹ := by
    simp [occupiedGaugeActionMultiplier, hi, left, left', x0]
  have hmJ :
      occupiedGaugeActionMultiplier rho iota cls a h j i =
        right' y0 * (right y0)⁻¹ := by
    simp [occupiedGaugeActionMultiplier, hj, right, right', y0]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hr := hleft (⟨x, hx⟩ : X)
    change a (rho h x) (iota h j) =
      (left' x0 * (left x0)⁻¹) * a x j at hr
    rw [← hmI] at hr
    exact hr
  · intro y hy
    have hr := hright (⟨y, hy⟩ : Y)
    change a (rho h y) (iota h i) =
      (right' y0 * (right y0)⁻¹) * a y i at hr
    rw [← hmJ] at hr
    exact hr
  · change s.normalized (left' x0 * (left x0)⁻¹) *
      (K (iota h i) (iota h j))⁻¹ *
        (right' y0 * (right y0)⁻¹) =
          (K i j)⁻¹ at hskeleton
    rw [← hmI, ← hmJ] at hskeleton
    exact hskeleton

end SemigenericEPPA
