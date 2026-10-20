import SemigenericEPPA.Algebra.IndexedGaugeHActionMatrix
import SemigenericEPPA.Algebra.OccupiedGaugeMultiplierStrictCocycle
import SemigenericEPPA.Algebra.OccupiedSkeletonNeutralCompletion

/-!
# One fixed good skeleton and genuine occupied H-multipliers

The previously separate nontrivial-G algebraic gates can be instantiated
from an ACTUAL H-action on an indexed old gauge presentation.

The effective H-invariance hypothesis implies the entire noncommutative
rank-one gauge matrix identity. This produces explicit canonical occupied
pair multipliers, whose neutral completion obeys the strict H-cocycle.
A reversal-fixed raw colour selects a COMPLETE skeleton independently
of H, rho, iota, and every later partial map. Every such genuine old
H-action preserves that very same skeleton by its completed multipliers.

In particular, neither the matrix identity nor the multiplier/skeleton
equations are extra input assumptions for consumers of this interface.

This proves the old-index algebraic package. It does NOT yet construct
the action on the larger valuation-witness part sort or on the final
raw residual-cover witness.
-/

namespace SemigenericEPPA

universe u v w t q

variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {I : Type t}
variable {H : Type q} [Group H]
variable {d : RawDatum G C}

namespace IndexedGauge

/-- An indexed old E-class is occupied precisely when a genuine old
vertex carries that index. Unused indices need no old coordinate. -/
def occupied (P : IndexedGauge d.s V I) (i : I) : Prop :=
  ∃ x : V, P.label x = i

/-- Choose the full skeleton before choosing any H-action.
The same genuinely self-reversing raw colour supplies the default
for all pairs with an unused endpoint and every diagonal pair. -/
noncomputable def fixedGoodSkeleton
    (P : IndexedGauge d.s V I)
    (hGood : d.selfReverseEffective.Nonempty) (i j : I) : G :=
  completeOccupiedSkeleton P.occupied P.skeleton (Classical.choose hGood) i j

/-- The actual anchored multipliers of an old H-action, completed
neutrally on pairs not represented by distinct occupied E-classes. -/
noncomputable def oldActionMultipliers
    (P : IndexedGauge d.s V I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (h : H) (i j : I) : G :=
  completeOccupiedGaugeMultipliers P.occupied
    (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge) h i j

/-- The fixed skeleton reverses under the ORIGINAL affine s, even
when s(1) != 1. This choice does not depend on H at all. -/
theorem fixedGoodSkeleton_reverse
    (P : IndexedGauge d.s V I)
    (hGood : d.selfReverseEffective.Nonempty)
    (i j : I) (hij : i ≠ j) :
    P.fixedGoodSkeleton hGood j i =
      d.s (P.fixedGoodSkeleton hGood i j) := by
  have hfixed : d.s (Classical.choose hGood) =
      Classical.choose hGood :=
    d.selfReverseEffective_subset_fixed (Classical.choose_spec hGood)
  change completeOccupiedSkeleton P.occupied P.skeleton
      (Classical.choose hGood) j i =
    d.s (completeOccupiedSkeleton P.occupied P.skeleton
      (Classical.choose hGood) i j)
  exact completeOccupiedSkeleton_reverse d.s P.occupied P.skeleton
    (fun i j _ _ hij => P.skeleton_reverse i j hij)
    (Classical.choose hGood) hfixed i j hij

/-- The same fixed completion agrees literally with all prescribed
old skeleton values between distinct occupied E-classes. -/
theorem fixedGoodSkeleton_old
    (P : IndexedGauge d.s V I)
    (hGood : d.selfReverseEffective.Nonempty)
    (i j : I) (hi : P.occupied i) (hj : P.occupied j)
    (hij : i ≠ j) :
    P.fixedGoodSkeleton hGood i j = P.skeleton i j := by
  change completeOccupiedSkeleton P.occupied P.skeleton
      (Classical.choose hGood) i j = P.skeleton i j
  exact completeOccupiedSkeleton_occupied P.occupied P.skeleton
    (Classical.choose hGood) i j hi hj hij

/-- From genuine effective-colour preservation, the CANONICAL
old-action multipliers satisfy identity and strict noncommutative
composition on every ordered pair of indices (even unused ones).
No independently supplied gauge matrix equation is needed. -/
theorem oldActionMultipliers_group_laws
    (P : IndexedGauge d.s V I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hLabel : ∀ h : H, ∀ x : V,
      P.label (rho h x) = iota h (P.label x))
    (hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y) :
    (∀ i j : I, P.oldActionMultipliers rho iota 1 i j = 1) ∧
    (∀ (k h : H) (i j : I),
      P.oldActionMultipliers rho iota (k * h) i j =
        P.oldActionMultipliers rho iota k (iota h i) (iota h j) *
          P.oldActionMultipliers rho iota h i j) := by
  have hMatrix := P.matrix_invariant_of_effective_H_action
    rho iota hLabel hEffective
  exact completeOccupiedGaugeActionMultiplier_group_laws d.s
    rho iota P.label P.vertexGauge P.skeleton
    hLabel hMatrix

/-- The canonical completed multiplier transports EVERY old gauge
row to its H-image, not just the arbitrary anchor used to define it. -/
theorem oldActionMultipliers_transport
    (P : IndexedGauge d.s V I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hLabel : ∀ h : H, ∀ x : V,
      P.label (rho h x) = iota h (P.label x))
    (hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y)
    (h : H) (i j : I)
    (hi : P.occupied i) (hj : P.occupied j)
    (hij : i ≠ j) (x : V) (hx : P.label x = i) :
    P.vertexGauge (rho h x) (iota h j) =
      P.oldActionMultipliers rho iota h i j * P.vertexGauge x j := by
  have hMatrix := P.matrix_invariant_of_effective_H_action
    rho iota hLabel hEffective
  have hRow := (occupiedGaugeActionMultiplier_preserves_old_pair
    d.s rho iota P.label P.vertexGauge P.skeleton
    hMatrix h i j hi hj hij).1 x hx
  change P.vertexGauge (rho h x) (iota h j) =
    completeOccupiedGaugeMultipliers P.occupied
      (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
      h i j * P.vertexGauge x j
  rw [completeOccupiedGaugeMultipliers_occupied P.occupied
    (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
    h i j hi hj hij]
  exact hRow

/-- The same H-INDEPENDENT fixed skeleton obeys the exact full
affine multiplier equation for ANY genuine old effective H-action.
The full quotient index set includes unused classes. -/
theorem fixedGoodSkeleton_preserved
    (P : IndexedGauge d.s V I)
    (hGood : d.selfReverseEffective.Nonempty)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hLabel : ∀ h : H, ∀ x : V,
      P.label (rho h x) = iota h (P.label x))
    (hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y)
    (h : H) (i j : I) (hij : i ≠ j) :
    d.s.normalized (P.oldActionMultipliers rho iota h i j) *
        (P.fixedGoodSkeleton hGood (iota h i) (iota h j))⁻¹ *
          P.oldActionMultipliers rho iota h j i =
      (P.fixedGoodSkeleton hGood i j)⁻¹ := by
  have hOcc : ∀ (h : H) (i : I),
      P.occupied (iota h i) ↔ P.occupied i := by
    intro h i
    change (∃ x : V, P.label x = iota h i) ↔
      (∃ x : V, P.label x = i)
    exact occupiedGaugeClass_hInvariant rho iota P.label
      hLabel h i
  have hMatrix := P.matrix_invariant_of_effective_H_action
    rho iota hLabel hEffective
  have hMSkeleton : ∀ (h : H) (i j : I),
      P.occupied i → P.occupied j → i ≠ j →
      d.s.normalized
          (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge
            h i j) *
        (P.skeleton (iota h i) (iota h j))⁻¹ *
          occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge
            h j i = (P.skeleton i j)⁻¹ := by
    intro h i j hi hj hij
    exact (occupiedGaugeActionMultiplier_preserves_old_pair
      d.s rho iota P.label P.vertexGauge P.skeleton
      hMatrix h i j hi hj hij).2.2
  change d.s.normalized
      (completeOccupiedGaugeMultipliers P.occupied
        (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
        h i j) *
      (completeOccupiedSkeleton P.occupied P.skeleton
        (Classical.choose hGood) (iota h i) (iota h j))⁻¹ *
      completeOccupiedGaugeMultipliers P.occupied
        (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
        h j i =
      (completeOccupiedSkeleton P.occupied P.skeleton
        (Classical.choose hGood) i j)⁻¹
  exact completedOccupiedSkeleton_multiplier_condition
    d.s iota P.occupied hOcc P.skeleton (Classical.choose hGood)
      (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
      hMSkeleton h i j hij

end IndexedGauge

end SemigenericEPPA
