import SemigenericEPPA.Algebra.IndexedGaugeFixedGoodHAction
import Mathlib.Tactic.Group

/-!
# Diagonal completion of the fixed-good H-multiplier skeleton

The one fixed good skeleton, certified on DISTINCT indices in the
occupied-gauge theorem, must also satisfy the reversal and affine
multiplier identities at i=j. There is a real reason to prove this:
two distinct witness valuation parts q=(i,f),r=(i,g) may project
to the SAME original class index i. Thus the strict action on
the entire valuation witness requires diagonal index equations.

Our selected fixed-good skeleton has the SAME s-fixed g0 on every
index diagonal, and the canonical occupied multipliers are 1
there. Therefore all diagonal identities follow without assuming
s(1)=1 or commutativity, and without modifying any off-diagonal
multipliers. The completion K itself was chosen before H.

This is an exact missing bridge to the old-index-to-witness-part
pullback action, not by itself an effective or raw EPPA witness.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {I : Type t}
variable {H : Type q} [Group H]
variable {d : RawDatum G C}

namespace IndexedGauge

/-- Full affine reversal including i=j. Unlike the usual
skeleton reversal law, this holds on ALL ordered index pairs.
A fixed good raw colour provides the diagonal fixed point. -/
theorem fixedGoodSkeleton_reverse_all
    (P : IndexedGauge d.s V I)
    (hGood : d.selfReverseEffective.Nonempty)
    (i j : I) :
    P.fixedGoodSkeleton hGood j i =
      d.s (P.fixedGoodSkeleton hGood i j) := by
  by_cases hij : i ≠ j
  · exact P.fixedGoodSkeleton_reverse hGood i j hij
  · have heq : i = j := not_ne_iff.mp hij
    subst j
    have hbad : ¬(P.occupied i ∧ P.occupied i ∧ i ≠ i) := by
      rintro ⟨_, _, hne⟩
      exact hne rfl
    change completeOccupiedSkeleton P.occupied P.skeleton
        (Classical.choose hGood) i i =
      d.s (completeOccupiedSkeleton P.occupied P.skeleton
        (Classical.choose hGood) i i)
    rw [completeOccupiedSkeleton_default P.occupied P.skeleton
      (Classical.choose hGood) i i hbad]
    exact (d.selfReverseEffective_subset_fixed
      (Classical.choose_spec hGood)).symm

/-- Actual old effective H-automorphisms preserve the SAME fixed
good skeleton on every index pair, including diagonals. This is
stronger than the off-diagonal law required on old structures and
exactly what the blown-up two-layer witness needs. -/
theorem fixedGoodSkeleton_preserved_all
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
    (h : H) (i j : I) :
    d.s.normalized (P.oldActionMultipliers rho iota h i j) *
        (P.fixedGoodSkeleton hGood (iota h i) (iota h j))⁻¹ *
          P.oldActionMultipliers rho iota h j i =
      (P.fixedGoodSkeleton hGood i j)⁻¹ := by
  by_cases hij : i ≠ j
  · exact P.fixedGoodSkeleton_preserved hGood rho iota
      hLabel hEffective h i j hij
  · have heq : i = j := not_ne_iff.mp hij
    subst j
    have hbad : ¬(P.occupied i ∧ P.occupied i ∧ i ≠ i) := by
      rintro ⟨_, _, hne⟩
      exact hne rfl
    have hbad' :
        ¬(P.occupied (iota h i) ∧ P.occupied (iota h i) ∧
          iota h i ≠ iota h i) := by
      rintro ⟨_, _, hne⟩
      exact hne rfl
    change d.s.normalized
        (completeOccupiedGaugeMultipliers P.occupied
          (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
          h i i) *
        (completeOccupiedSkeleton P.occupied P.skeleton
          (Classical.choose hGood) (iota h i) (iota h i))⁻¹ *
        completeOccupiedGaugeMultipliers P.occupied
          (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
          h i i =
      (completeOccupiedSkeleton P.occupied P.skeleton
        (Classical.choose hGood) i i)⁻¹
    rw [completeOccupiedGaugeMultipliers_default P.occupied
        (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
        h i i hbad,
      completeOccupiedSkeleton_default P.occupied P.skeleton
        (Classical.choose hGood) (iota h i) (iota h i) hbad',
      completeOccupiedSkeleton_default P.occupied P.skeleton
        (Classical.choose hGood) i i hbad]
    unfold AffineAntiInvolution.normalized
    group

end IndexedGauge

end SemigenericEPPA
