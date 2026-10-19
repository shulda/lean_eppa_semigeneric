import SemigenericEPPA.Algebra.EffectiveGroupGaugeCocycles

/-!
# Completing occupied-part gauge cocycles by neutral defaults

The full-group effective lift in manuscript §4 defines the pair
multiplier M^h_{ij} on pairs of distinct OCCUPIED old E-part indices.
For any pair touching an unoccupied part, or a diagonal pair, it
uses the neutral multiplier 1.

The occupied subset is invariant under the H-action on E-part indices.
Consequently, the case distinction is invariant. The strict
noncommutative multiplier cocycle established on occupied pairs in
(4.26) extends to ALL ordered index pairs, with identity at h=1.

This closes a quantifier/totalization gap: the full valuation
transport requires multipliers on every pair, not merely the
occupied ones. It does not assert the separate affine skeleton
equation or construct the occupied group multipliers themselves.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {I : Type v} {G : Type w} [Group G]

/-- Retain the genuine occupied pair multiplier on distinct occupied
indices; set all remaining values to the identity element. -/
noncomputable def completeOccupiedGaugeMultipliers
    (occupied : I → Prop)
    (M : H → I → I → G)
    (h : H) (i j : I) : G := by
  classical
  exact if occupied i ∧ occupied j ∧ i ≠ j then
    M h i j else 1

/-- Occupied inputs are preserved exactly, including the intended
multiplication order in noncommutative G. -/
theorem completeOccupiedGaugeMultipliers_occupied
    (occupied : I → Prop) (M : H → I → I → G)
    (h : H) (i j : I)
    (hi : occupied i) (hj : occupied j) (hij : i ≠ j) :
    completeOccupiedGaugeMultipliers occupied M h i j = M h i j := by
  classical
  simp [completeOccupiedGaugeMultipliers, hi, hj, hij]

/-- The chosen neutral defaults apply on all non-occupied and
diagonal pairs; no group property is needed for this assertion. -/
theorem completeOccupiedGaugeMultipliers_default
    (occupied : I → Prop) (M : H → I → I → G)
    (h : H) (i j : I)
    (hbad : ¬(occupied i ∧ occupied j ∧ i ≠ j)) :
    completeOccupiedGaugeMultipliers occupied M h i j = 1 := by
  classical
  simp [completeOccupiedGaugeMultipliers, hbad]

/-- The extension to all pairs preserves the strict group identity
and the full noncommutative cocycle, provided H permutes occupied
indices and the genuine occupied multipliers have the corresponding
identity and cocycle equations. -/
theorem completeOccupiedGaugeMultipliers_group_laws
    (iota : H →* Equiv.Perm I)
    (occupied : I → Prop)
    (hoccupied : ∀ (h : H) (i : I),
      occupied (iota h i) ↔ occupied i)
    (M : H → I → I → G)
    (hMone : ∀ i j, occupied i → occupied j → i ≠ j →
      M 1 i j = 1)
    (hMmul : ∀ (k h : H) (i j : I),
      occupied i → occupied j → i ≠ j →
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j) :
    (∀ i j : I,
      completeOccupiedGaugeMultipliers occupied M 1 i j = 1) ∧
    (∀ (k h : H) (i j : I),
      completeOccupiedGaugeMultipliers occupied M (k * h) i j =
        completeOccupiedGaugeMultipliers occupied M k
          (iota h i) (iota h j) *
          completeOccupiedGaugeMultipliers occupied M h i j) := by
  classical
  constructor
  · intro i j
    by_cases hp : occupied i ∧ occupied j ∧ i ≠ j
    · rw [completeOccupiedGaugeMultipliers_occupied
        occupied M 1 i j hp.1 hp.2.1 hp.2.2]
      exact hMone i j hp.1 hp.2.1 hp.2.2
    · exact completeOccupiedGaugeMultipliers_default
        occupied M 1 i j hp
  · intro k h i j
    by_cases hp : occupied i ∧ occupied j ∧ i ≠ j
    · have hp' : occupied (iota h i) ∧
          occupied (iota h j) ∧ iota h i ≠ iota h j :=
        ⟨(hoccupied h i).mpr hp.1,
          (hoccupied h j).mpr hp.2.1,
          (iota h).injective.ne hp.2.2⟩
      rw [completeOccupiedGaugeMultipliers_occupied
          occupied M (k * h) i j hp.1 hp.2.1 hp.2.2,
        completeOccupiedGaugeMultipliers_occupied
          occupied M k (iota h i) (iota h j)
          hp'.1 hp'.2.1 hp'.2.2,
        completeOccupiedGaugeMultipliers_occupied
          occupied M h i j hp.1 hp.2.1 hp.2.2]
      exact hMmul k h i j hp.1 hp.2.1 hp.2.2
    · have hp' : ¬(occupied (iota h i) ∧
          occupied (iota h j) ∧ iota h i ≠ iota h j) := by
        rintro ⟨hi,hj,hij⟩
        apply hp
        refine ⟨(hoccupied h i).mp hi,
          (hoccupied h j).mp hj, ?_⟩
        intro heq
        exact hij (congrArg (iota h) heq)
      rw [completeOccupiedGaugeMultipliers_default
          occupied M (k * h) i j hp,
        completeOccupiedGaugeMultipliers_default
          occupied M k (iota h i) (iota h j) hp',
        completeOccupiedGaugeMultipliers_default
          occupied M h i j hp]
      exact (one_mul (1 : G)).symm

end SemigenericEPPA
