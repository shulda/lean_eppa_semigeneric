import SemigenericEPPA.Algebra.IndexedGaugeFixedGoodHAction

/-!
# Transport of every original gauge row, including the diagonal

The occupied multiplier construction proves old-row transport on
DISTINCT occupied E-classes. This lemma makes the missing diagonal
condition explicit and closes that final old-gauge compatibility
when EVERY index is occupied.

Diagonal old gauge values are not determined by the group-valued
cross-E relation (the same-E effective value is dummy). Hence one
must normalize or otherwise prove their equivariance; it is NOT a
consequence of the rectangle law. The completed multiplier is 1
on the index diagonal, so the extra condition is exactly literal
equivariance of the diagonal old gauge coordinate.

This theorem is tailored to quotients indexed by their actual old
E-classes, which are all inhabited, and is reusable in the pointwise
old-vertex extension gate of the two-layer witness.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {I : Type t}
variable {H : Type q} [Group H]
variable {d : RawDatum G C}

namespace IndexedGauge

/-- All-index old-row transport for the genuinely constructed
H-multipliers, provided the original E-index map is surjective
and diagonal gauges are H-invariant. Off-diagonal transport is
deduced from actual effective H-automorphisms, rather than assumed. -/
theorem oldActionMultipliers_transport_all
    (P : IndexedGauge d.s V I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hSurj : Function.Surjective P.label)
    (hLabel : ∀ h : H, ∀ x : V,
      P.label (rho h x) = iota h (P.label x))
    (hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y)
    (hDiagonal : ∀ (h : H) (x : V),
      P.vertexGauge (rho h x) (iota h (P.label x)) =
        P.vertexGauge x (P.label x))
    (h : H) (x : V) (j : I) :
    P.vertexGauge (rho h x) (iota h j) =
      P.oldActionMultipliers rho iota h (P.label x) j *
        P.vertexGauge x j := by
  by_cases hdiag : P.label x = j
  · subst j
    have hbad : ¬(P.occupied (P.label x) ∧
        P.occupied (P.label x) ∧ P.label x ≠ P.label x) := by
      rintro ⟨_, _, hne⟩
      exact hne rfl
    have hm :
        P.oldActionMultipliers rho iota h (P.label x) (P.label x) = 1 := by
      exact completeOccupiedGaugeMultipliers_default
        P.occupied
        (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
        h (P.label x) (P.label x) hbad
    rw [hm, one_mul]
    exact hDiagonal h x
  · exact P.oldActionMultipliers_transport rho iota
      hLabel hEffective h (P.label x) j
      ⟨x, rfl⟩ (hSurj j) hdiag x rfl

end IndexedGauge

end SemigenericEPPA
