import SemigenericEPPA.Algebra.IndexedGaugeFixedGoodHAction

/-!
# Complete old-row transport including its diagonal

The genuine occupied-gauge multipliers M_h(i,j) already transport
all old rows when i and j are DISTINCT occupied class indices.
The literal old-vertex H-lift also needs the diagonal j=i, because
different blown-up valuation parts can have the same old class index.

For a normalized old gauge, a(x,cls(x))=1. The chosen multiplier
M_h(i,i) is 1 by definition, so the diagonal transport equation
follows immediately and consistently for all h. Together with the
certified occupied-pair transport this gives ONE exact row equation
on every occupied target index, with no recentering or commutativity.

Unoccupied indices are deliberately excluded: there are no old
rows there, and an unconstrained gauge value cannot be expected
to transform equivariantly without an auxiliary reference twist.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {I : Type t}
variable {H : Type q} [Group H]
variable {d : RawDatum G C}

namespace IndexedGauge

/-- The canonical occupied gauge multiplier transports every old
row towards every actually inhabited class index, INCLUDING the
diagonal, if all source-class gauge coordinates are normalized to 1. -/
theorem oldActionMultipliers_transport_all_occupied
    (P : IndexedGauge d.s V I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hLabel : ∀ h : H, ∀ x : V,
      P.label (rho h x) = iota h (P.label x))
    (hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y)
    (hDiagonal : ∀ x : V,
      P.vertexGauge x (P.label x) = 1)
    (h : H) (x : V) (j : I)
    (hj : P.occupied j) :
    P.oldActionMultipliers rho iota h (P.label x) j *
      P.vertexGauge x j =
        P.vertexGauge (rho h x) (iota h j) := by
  by_cases hij : P.label x ≠ j
  · exact (P.oldActionMultipliers_transport
      rho iota hLabel hEffective h (P.label x) j
      ⟨x, rfl⟩ hj hij x rfl).symm
  · have heq : P.label x = j := Classical.not_not.mp hij
    subst j
    have hbad : ¬(P.occupied (P.label x) ∧
        P.occupied (P.label x) ∧ P.label x ≠ P.label x) := by
      rintro ⟨_, _, hne⟩
      exact hne rfl
    have hM :
        P.oldActionMultipliers rho iota h (P.label x) (P.label x) = 1 := by
      change completeOccupiedGaugeMultipliers P.occupied
        (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
          h (P.label x) (P.label x) = 1
      exact completeOccupiedGaugeMultipliers_default
        P.occupied
        (occupiedGaugeActionMultiplier rho iota P.label P.vertexGauge)
        h (P.label x) (P.label x) hbad
    rw [hM, one_mul, hDiagonal x]
    rw [← hLabel h x]
    exact (hDiagonal (rho h x)).symm

end IndexedGauge

end SemigenericEPPA
