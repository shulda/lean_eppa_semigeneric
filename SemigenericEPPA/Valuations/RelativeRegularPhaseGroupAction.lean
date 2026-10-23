import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

/-!
# Relative DLF regular-phase blow-up for an arbitrary H-action

Let H act on a base set V and let S⊆V be H-invariant.
The phase-lift has carrier V×H and acts by
  h·(x,r) = (h·x,r)   if x∈S,
          = (h·x,hr)  if x∉S.
Its inverse uses h⁻¹ and the SAME H-invariant subset.

This preserves a distinguished phase-one copy on S literally.
Outside S, a group element swapping two phase vertices must
satisfy h²=1, because the phase coordinate is regular.
That order-two conclusion is FALSE on S and is deliberately
not asserted there: an element of order four can swap vertices
in the original old sector without being an involution.

The distinction is essential in the audited relative safe-group
EPPA construction under ONE complete good congruence orbit.
No finite geometry, raw palette or group cover is used here.
-/

namespace SemigenericEPPA

universe u v
variable {H : Type u} [Group H] {V : Type v}

/-- Explicit invertible action on base points with a regular
phase factor only outside the distinguished invariant subset. -/
noncomputable def relativePhasePerm
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (h : H) : (V × H) ≃ (V × H) := by
  classical
  refine {
    toFun := fun X =>
      (rho h X.1, if X.1 ∈ S then X.2 else h * X.2)
    invFun := fun Y =>
      (rho h⁻¹ Y.1, if Y.1 ∈ S then Y.2 else h⁻¹ * Y.2)
    left_inv := ?_
    right_inv := ?_
  }
  · rintro ⟨x, r⟩
    have hbase : rho h⁻¹ (rho h x) = x := by
      calc
        rho h⁻¹ (rho h x) = rho (h⁻¹ * h) x := by rw [map_mul]; rfl
        _ = x := by simp
    change (rho h⁻¹ (rho h x),
      if rho h x ∈ S then
        (if x ∈ S then r else h * r)
      else h⁻¹ * (if x ∈ S then r else h * r)) = (x, r)
    by_cases hx : x ∈ S
    · have hy : rho h x ∈ S := (hS h x).mp hx
      simp [hx, hy, hbase]
    · have hy : rho h x ∉ S := fun z => hx ((hS h x).mpr z)
      simp [hx, hy, hbase]
  · rintro ⟨y, r⟩
    have hbase : rho h (rho h⁻¹ y) = y := by
      calc
        rho h (rho h⁻¹ y) = rho (h * h⁻¹) y := by rw [map_mul]; rfl
        _ = y := by simp
    change (rho h (rho h⁻¹ y),
      if rho h⁻¹ y ∈ S then
        (if y ∈ S then r else h⁻¹ * r)
      else h * (if y ∈ S then r else h⁻¹ * r)) = (y, r)
    by_cases hy : y ∈ S
    · have hx : rho h⁻¹ y ∈ S := (hS h⁻¹ y).mp hy
      simp [hy, hx, hbase]
    · have hx : rho h⁻¹ y ∉ S := fun z => hy ((hS h⁻¹ y).mpr z)
      simp [hy, hx, hbase]

/-- Strict group action on the complete phase-blown-up carrier. -/
noncomputable def relativePhaseAction
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S) :
    H →* Equiv.Perm (V × H) where
  toFun := relativePhasePerm rho S hS
  map_one' := by
    apply Equiv.ext
    rintro ⟨x,r⟩
    by_cases hx : x ∈ S <;>
      simp [relativePhasePerm, hx]
  map_mul' := by
    intro h k
    apply Equiv.ext
    rintro ⟨x,r⟩
    by_cases hx : x ∈ S
    · have hk : rho k x ∈ S := (hS k x).mp hx
      simp [relativePhasePerm, hx, hk, map_mul]
    · have hk : rho k x ∉ S :=
        fun z => hx ((hS k x).mpr z)
      simp [relativePhasePerm, hx, hk, map_mul, mul_assoc]

/-- The base projection commutes with the actual H action. -/
theorem relativePhaseAction_base
    (rho : H →* Equiv.Perm V) (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (h : H) (X : V × H) :
    (relativePhaseAction rho S hS h X).1 = rho h X.1 := rfl

/-- The designated zero-section over S has trivial phase and
extends the old group action EXACTLY. -/
theorem relativePhaseAction_old
    (rho : H →* Equiv.Perm V) (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (h : H) (x : V) (hx : x ∈ S) :
    relativePhaseAction rho S hS h (x, (1 : H)) =
      (rho h x, (1 : H)) := by
  simp [relativePhaseAction, relativePhasePerm, hx]

/-- Outside the original distinguished S, a group element
that swaps two phase vertices MUST square to the identity.
Do NOT invoke this lemma inside S. -/
theorem relativePhaseAction_swapOutside_square_one
    (rho : H →* Equiv.Perm V) (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (h : H) (X Y : V × H)
    (hX : X.1 ∉ S)
    (hXY : relativePhaseAction rho S hS h X = Y)
    (hYX : relativePhaseAction rho S hS h Y = X) :
    h * h = 1 := by
  have hY : Y.1 ∉ S := by
    intro hy
    have hbaseXY : rho h X.1 = Y.1 :=
      (relativePhaseAction_base rho S hS h X).symm.trans
        (congrArg Prod.fst hXY)
    have hx : rho h X.1 ∈ S := by
      rw [hbaseXY]
      exact hy
    exact hX ((hS h X.1).mpr hx)
  have hp : h * X.2 = Y.2 := by
    have z := congrArg Prod.snd hXY
    simpa [relativePhaseAction, relativePhasePerm, hX] using z
  have hq : h * Y.2 = X.2 := by
    have z := congrArg Prod.snd hYX
    simpa [relativePhaseAction, relativePhasePerm, hY] using z
  have htr : (h * h) * X.2 = (1 : H) * X.2 := by
    calc
      (h * h) * X.2 = h * (h * X.2) := by group
      _ = h * Y.2 := by rw [hp]
      _ = X.2 := hq
      _ = 1 * X.2 := by simp
  exact mul_right_cancel htr

end SemigenericEPPA
