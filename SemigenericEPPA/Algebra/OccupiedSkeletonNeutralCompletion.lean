import SemigenericEPPA.Algebra.OccupiedGaugeCocycleCompletion
import SemigenericEPPA.Algebra.SkeletonMultipliers
import Mathlib.Tactic.Group

/-!
# Affine skeleton completion by one reversal-fixed effective colour

In the full-group positive coherent construction for arbitrary G,
the original old occupied-occupied E-part pairs carry a prescribed
skeleton K(i,j), while any pair touching an UNUSED part index can
be assigned one canonical effective colour g0 fixed by the affine
reversal s.

On diagonals and pairs touching unused indices we also choose the
neutral multiplier m_h(i,j)=1. This preserves the exact affine
skeleton automorphism equation (3.9) automatically provided the
occupied subset of part indices is H-invariant.

On both occupied source indices, the completed skeleton agrees
with K literally, including after transport by H, so the
pre-existing prescribed affine/noncommutative skeleton equation
passes unchanged.

This is a missing gluing gate between the occupied-pair
multipliers and the full two-layer witness action: no false
assumption s(1)=1 is made. A self-reversing old raw colour
supplies the required g0 since d.phi(c)=s(d.phi(c)).
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {I : Type v} {H : Type w} [Group H]

/-- The full skeleton agrees with its prescribed old K on distinct
occupied pairs and equals the SAME reversal-fixed g0 on all other
ordered pairs. -/
noncomputable def completeOccupiedSkeleton
    (occupied : I → Prop) (K : I → I → G)
    (g0 : G) (i j : I) : G := by
  classical
  exact if occupied i ∧ occupied j ∧ i ≠ j then K i j else g0

theorem completeOccupiedSkeleton_occupied
    (occupied : I → Prop) (K : I → I → G)
    (g0 : G) (i j : I)
    (hi : occupied i) (hj : occupied j) (hij : i ≠ j) :
    completeOccupiedSkeleton occupied K g0 i j = K i j := by
  classical
  simp [completeOccupiedSkeleton, hi, hj, hij]

theorem completeOccupiedSkeleton_default
    (occupied : I → Prop) (K : I → I → G)
    (g0 : G) (i j : I)
    (hbad : ¬(occupied i ∧ occupied j ∧ i ≠ j)) :
    completeOccupiedSkeleton occupied K g0 i j = g0 := by
  classical
  simp [completeOccupiedSkeleton, hbad]

/-- Old skeleton reversal on occupied pairs plus ONE genuinely
s-fixed default gives the correct affine reversal on EVERY
distinct pair of the fixed complete index set. -/
theorem completeOccupiedSkeleton_reverse
    (s : AffineAntiInvolution G)
    (occupied : I → Prop)
    (K : I → I → G)
    (hK : ∀ i j : I, occupied i → occupied j →
      i ≠ j → K j i = s (K i j))
    (g0 : G) (hg0 : s g0 = g0)
    (i j : I) (hij : i ≠ j) :
    completeOccupiedSkeleton occupied K g0 j i =
      s (completeOccupiedSkeleton occupied K g0 i j) := by
  classical
  by_cases hp : occupied i ∧ occupied j ∧ i ≠ j
  · have hprev : occupied j ∧ occupied i ∧ j ≠ i :=
      ⟨hp.2.1, hp.1, hp.2.2.symm⟩
    rw [completeOccupiedSkeleton_occupied occupied K g0
      j i hprev.1 hprev.2.1 hprev.2.2,
      completeOccupiedSkeleton_occupied occupied K g0
      i j hp.1 hp.2.1 hp.2.2]
    exact hK i j hp.1 hp.2.1 hp.2.2
  · have hbadReverse : ¬(occupied j ∧ occupied i ∧ j ≠ i) := by
      rintro ⟨hj,hi,hji⟩
      exact hp ⟨hi,hj,hji.symm⟩
    rw [completeOccupiedSkeleton_default occupied K g0
      j i hbadReverse,
      completeOccupiedSkeleton_default occupied K g0 i j hp]
    exact hg0.symm

/-- Full skeleton compatibility on the complete witness index
set from (i) the canonical old occupied-pair equations and
(ii) neutral unoccupied-pair choices. Works for any nonabelian
group and any affine anti-involution s, including s(1)≠1. -/
theorem completedOccupiedSkeleton_multiplier_condition
    (s : AffineAntiInvolution G)
    (iota : H →* Equiv.Perm I)
    (occupied : I → Prop)
    (hOcc : ∀ (h : H) (i : I),
      occupied (iota h i) ↔ occupied i)
    (K : I → I → G)
    (g0 : G)
    (M : H → I → I → G)
    (hOccupiedSkeleton : ∀ (h : H) (i j : I),
      occupied i → occupied j → i ≠ j →
      s.normalized (M h i j) *
          (K (iota h i) (iota h j))⁻¹ *
            M h j i = (K i j)⁻¹)
    (h : H) (i j : I) (hij : i ≠ j) :
    s.normalized
        (completeOccupiedGaugeMultipliers occupied M h i j) *
      (completeOccupiedSkeleton occupied K g0
        (iota h i) (iota h j))⁻¹ *
        completeOccupiedGaugeMultipliers occupied M h j i =
      (completeOccupiedSkeleton occupied K g0 i j)⁻¹ := by
  classical
  by_cases hp : occupied i ∧ occupied j ∧ i ≠ j
  · have hprev : occupied j ∧ occupied i ∧ j ≠ i :=
      ⟨hp.2.1, hp.1, hp.2.2.symm⟩
    have hpnext : occupied (iota h i) ∧
        occupied (iota h j) ∧
        iota h i ≠ iota h j :=
      ⟨(hOcc h i).mpr hp.1, (hOcc h j).mpr hp.2.1,
        (iota h).injective.ne hp.2.2⟩
    rw [completeOccupiedGaugeMultipliers_occupied
        occupied M h i j hp.1 hp.2.1 hp.2.2,
      completeOccupiedGaugeMultipliers_occupied
        occupied M h j i hprev.1 hprev.2.1 hprev.2.2,
      completeOccupiedSkeleton_occupied
        occupied K g0 (iota h i) (iota h j)
        hpnext.1 hpnext.2.1 hpnext.2.2,
      completeOccupiedSkeleton_occupied
        occupied K g0 i j hp.1 hp.2.1 hp.2.2]
    exact hOccupiedSkeleton h i j hp.1 hp.2.1 hp.2.2
  · have hpback : ¬(occupied j ∧ occupied i ∧ j ≠ i) := by
      rintro ⟨hj, hi, hji⟩
      exact hp ⟨hi,hj,hji.symm⟩
    have hpnext : ¬(occupied (iota h i) ∧
        occupied (iota h j) ∧ iota h i ≠ iota h j) := by
      rintro ⟨hi,hj,_⟩
      exact hp ⟨(hOcc h i).mp hi, (hOcc h j).mp hj, hij⟩
    rw [completeOccupiedGaugeMultipliers_default occupied M h i j hp,
      completeOccupiedGaugeMultipliers_default occupied M h j i hpback,
      completeOccupiedSkeleton_default occupied K g0
        (iota h i) (iota h j) hpnext,
      completeOccupiedSkeleton_default occupied K g0 i j hp]
    unfold AffineAntiInvolution.normalized
    group

end SemigenericEPPA
