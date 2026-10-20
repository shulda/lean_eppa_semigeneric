import SemigenericEPPA.Algebra.OccupiedGaugeMultiplierAction
import SemigenericEPPA.Algebra.OccupiedGaugeCocycleCompletion
import Mathlib.Tactic.Group

/-!
# Genuine noncommutative H-cocycle of occupied gauge multipliers

The anchored old-gauge multiplier family from the previous module
satisfies the noncommutative strict action law
  m_(k*h)(i,j) = m_k(h i,h j) * m_h(i,j)
on every pair of DISTINCT OCCUPIED old E-classes.

Proof: both sides transport the same old coordinate a(x,j) for
every old vertex x in source class i; cancel this coordinate.
In particular the law is a consequence of the real H-action and
literal old cross-colour invariance, not of independently chosen
extensions for each h.

Occupation of part indices is H-invariant. Thus the neutral
completion m_h(i,j)=1 on every diagonal or pair touching unused
indices preserves BOTH the strict group identity and multiplication
laws on ALL ordered part pairs.

These algebraic gates feed the full valuation-witness action,
whose separate skeleton and raw flip-safety constraints must also
hold. No recentering, commutativity, or s(1)=1 is assumed.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {I : Type t}

/-- The genuine set of occupied E-part indices is invariant under
an H-action whose vertex and index permutations preserve cls. -/
theorem occupiedGaugeClass_hInvariant
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (hcls : ∀ h : H, ∀ x : V,
      cls (rho h x) = iota h (cls x))
    (h : H) (i : I) :
    (∃ x : V, cls x = iota h i) ↔ (∃ x : V, cls x = i) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(rho h).symm y, ?_⟩
    have hc := hcls h ((rho h).symm y)
    rw [(rho h).apply_symm_apply] at hc
    exact (iota h).injective (hc.symm.trans hy)
  · rintro ⟨x, hx⟩
    exact ⟨rho h x, by rw [hcls h x, hx]⟩

/-- Arbitrary multipliers which realize the actual H-action on all
old coordinates of each distinct occupied E-part pair MUST form
a genuine noncommutative group cocycle on these pairs. -/
theorem occupiedGaugeMultipliers_cocycle_of_transport
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (m : H → I → I → G)
    (hcls : ∀ h : H, ∀ x : V,
      cls (rho h x) = iota h (cls x))
    (hrow : ∀ (h : H) (i j : I),
      (∃ x : V, cls x = i) →
      (∃ y : V, cls y = j) →
      i ≠ j →
      ∀ x : V, cls x = i →
        a (rho h x) (iota h j) = m h i j * a x j)
    (k h : H) (i j : I)
    (hi : ∃ x : V, cls x = i)
    (hj : ∃ y : V, cls y = j)
    (hij : i ≠ j) :
    m (k * h) i j =
      m k (iota h i) (iota h j) * m h i j := by
  obtain ⟨x, hx⟩ := hi
  have hxi : cls (rho h x) = iota h i := by
    rw [hcls h x, hx]
  have hi' : ∃ z : V, cls z = iota h i := ⟨rho h x, hxi⟩
  have hj' : ∃ z : V, cls z = iota h j :=
    (occupiedGaugeClass_hInvariant rho iota cls hcls h j).mpr hj
  have hij' : iota h i ≠ iota h j :=
    (iota h).injective.ne hij
  have hh := hrow h i j ⟨x, hx⟩ hj hij x hx
  have hk := hrow k (iota h i) (iota h j)
    hi' hj' hij' (rho h x) hxi
  have hkh := hrow (k * h) i j ⟨x, hx⟩ hj hij x hx
  have hmulx : rho (k * h) x = rho k (rho h x) := by
    rw [map_mul]
    rfl
  have hmuli : iota (k * h) j = iota k (iota h j) := by
    rw [map_mul]
    rfl
  have hc :
      m (k * h) i j * a x j =
        (m k (iota h i) (iota h j) * m h i j) * a x j := by
    calc
      m (k * h) i j * a x j =
          a (rho (k * h) x) (iota (k * h) j) := hkh.symm
      _ = a (rho k (rho h x)) (iota k (iota h j)) := by
            rw [hmulx, hmuli]
      _ = m k (iota h i) (iota h j) *
          a (rho h x) (iota h j) := hk
      _ = (m k (iota h i) (iota h j) * m h i j) * a x j := by
            rw [hh]
            group
  exact mul_right_cancel hc

/-- The explicit anchored old gauge family satisfies the strict
noncommutative H-cocycle on every distinct occupied pair, provided
the original complete affine gauge cross-matrix is H-invariant. -/
theorem occupiedGaugeActionMultiplier_cocycle
    (s : AffineAntiInvolution G)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (K : I → I → G)
    (hcls : ∀ h : H, ∀ x : V,
      cls (rho h x) = iota h (cls x))
    (hMatrix : ∀ (h : H) (x y : V),
      cls x ≠ cls y →
      gaugeColour s (a x (cls y))
        (K (cls x) (cls y)) (a y (cls x)) =
      gaugeColour s
        (a (rho h x) (iota h (cls y)))
        (K (iota h (cls x)) (iota h (cls y)))
        (a (rho h y) (iota h (cls x))))
    (k h : H) (i j : I)
    (hi : ∃ x : V, cls x = i)
    (hj : ∃ y : V, cls y = j)
    (hij : i ≠ j) :
    occupiedGaugeActionMultiplier rho iota cls a (k * h) i j =
      occupiedGaugeActionMultiplier rho iota cls a k
        (iota h i) (iota h j) *
      occupiedGaugeActionMultiplier rho iota cls a h i j := by
  apply occupiedGaugeMultipliers_cocycle_of_transport
    rho iota cls a
      (occupiedGaugeActionMultiplier rho iota cls a) hcls
  · intro h' i' j' hi' hj' hij' x hx
    exact (occupiedGaugeActionMultiplier_preserves_old_pair
      s rho iota cls a K hMatrix h' i' j' hi' hj' hij').1 x hx
  · exact k
  · exact h
  · exact i
  · exact j
  · exact hi
  · exact hj
  · exact hij

/-- One single canonical TOTAL multiplier family exists for every
H-element and every ordered index pair, with neutral values on
unused/diagonal pairs and STRICT identity and composition equations
on the complete index set. -/
theorem completeOccupiedGaugeActionMultiplier_group_laws
    (s : AffineAntiInvolution G)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (cls : V → I)
    (a : V → I → G)
    (K : I → I → G)
    (hcls : ∀ h : H, ∀ x : V,
      cls (rho h x) = iota h (cls x))
    (hMatrix : ∀ (h : H) (x y : V),
      cls x ≠ cls y →
      gaugeColour s (a x (cls y))
        (K (cls x) (cls y)) (a y (cls x)) =
      gaugeColour s
        (a (rho h x) (iota h (cls y)))
        (K (iota h (cls x)) (iota h (cls y)))
        (a (rho h y) (iota h (cls x)))) :
    (∀ i j : I,
      completeOccupiedGaugeMultipliers
        (fun i => ∃ x : V, cls x = i)
        (occupiedGaugeActionMultiplier rho iota cls a)
        1 i j = 1) ∧
    (∀ (k h : H) (i j : I),
      completeOccupiedGaugeMultipliers
        (fun i => ∃ x : V, cls x = i)
        (occupiedGaugeActionMultiplier rho iota cls a)
        (k * h) i j =
      completeOccupiedGaugeMultipliers
        (fun i => ∃ x : V, cls x = i)
        (occupiedGaugeActionMultiplier rho iota cls a)
        k (iota h i) (iota h j) *
      completeOccupiedGaugeMultipliers
        (fun i => ∃ x : V, cls x = i)
        (occupiedGaugeActionMultiplier rho iota cls a)
        h i j) := by
  apply completeOccupiedGaugeMultipliers_group_laws
    iota (fun i => ∃ x : V, cls x = i)
      (fun h i =>
        occupiedGaugeClass_hInvariant rho iota cls hcls h i)
      (occupiedGaugeActionMultiplier rho iota cls a)
  · intro i j hi hj hij
    exact occupiedGaugeActionMultiplier_one rho iota cls a i j
  · intro k h i j hi hj hij
    exact occupiedGaugeActionMultiplier_cocycle
      s rho iota cls a K hcls hMatrix k h i j hi hj hij

end SemigenericEPPA
