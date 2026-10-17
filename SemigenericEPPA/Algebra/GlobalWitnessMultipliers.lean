import SemigenericEPPA.Algebra.SkeletonMultipliers
import Mathlib.Order.Basic

/-!
# A global choice of automorphism multipliers for arbitrary skeletons

The multiplier algebra of manuscript (3.9)--(3.10) already shows
that, for every unordered pair of distinct witness parts, an arbitrary
multiplier in one orientation uniquely forces the reverse multiplier.

Using an auxiliary linear order on the part set I, choose m(i,j)=1
when i<j, and define m(j,i) by the verified forced-reverse formula.
This satisfies the full noncommutative, AFFINE skeleton equation
  s(1)⁻¹ s(m(i,j)) K(σi,σj)⁻¹ m(j,i) = K(i,j)⁻¹
for EVERY ordered distinct pair. In the reverse orientation the
proof genuinely uses the affine involution, not commutativity.

The order is auxiliary; it is never part of the relational language.
No finiteness, self-reversing raw colour, EPPA extension theorem
or HKN existence theorem is assumed.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {I : Type v} [LinearOrder I]

/-- The global ordered-pair multiplier choice for a prescribed
permutation σ of witness parts. The diagonal does not matter.
A choice in the ascending direction determines the descending one. -/
noncomputable def globallyForcedWitnessMultiplier
    (s : AffineAntiInvolution G)
    (K : I → I → G) (σ : I ≃ I) (i j : I) : G := by
  classical
  exact if i = j then 1
    else if i < j then 1
    else eppeReverseMultiplier s (K j i) (K (σ j) (σ i)) 1

@[simp] theorem globallyForcedWitnessMultiplier_diag
    (s : AffineAntiInvolution G)
    (K : I → I → G) (σ : I ≃ I) (i : I) :
    globallyForcedWitnessMultiplier s K σ i i = 1 := by
  simp [globallyForcedWitnessMultiplier]

/-- Every ordered pair of distinct parts satisfies the original
skeleton multiplier equation (3.9), regardless of the permutation σ.
In particular, constraints for opposite orientations are consistent. -/
theorem globallyForcedWitnessMultiplier_equation
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (hK : ∀ i j : I, i ≠ j → K j i = s (K i j))
    (σ : I ≃ I) (i j : I) (hij : i ≠ j) :
    s.normalized (globallyForcedWitnessMultiplier s K σ i j) *
      (K (σ i) (σ j))⁻¹ *
        globallyForcedWitnessMultiplier s K σ j i =
      (K i j)⁻¹ := by
  classical
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hnot : ¬j < i := not_lt_of_ge (le_of_lt hlt)
    have h := eppe_reverseMultiplier_forward
      s (K i j) (K (σ i) (σ j)) 1
    simpa [globallyForcedWitnessMultiplier, hij, hij.symm,
      hlt, hnot] using h
  · have hnot : ¬i < j := not_lt_of_ge (le_of_lt hgt)
    have hk : K i j = s (K j i) := hK j i hij.symm
    have hsk : K (σ i) (σ j) =
        s (K (σ j) (σ i)) :=
      hK (σ j) (σ i) (σ.injective hij.symm)
    have h := eppe_reverseMultiplier_backward
      s (K j i) (K (σ j) (σ i)) 1
    simpa [globallyForcedWitnessMultiplier, hij, hij.symm,
      hgt, hnot, hk, hsk] using h

/-- The global data required by the effective automorphism
criterion are available for arbitrary σ and any reversible skeleton.
This result does NOT construct the vertex-coordinate permutation;
it discharges precisely its ordered multiplier existence obligation. -/
theorem exists_witnessMultipliers
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (hK : ∀ i j : I, i ≠ j → K j i = s (K i j))
    (σ : I ≃ I) :
    ∃ m : I → I → G,
      ∀ i j : I, i ≠ j →
        s.normalized (m i j) * (K (σ i) (σ j))⁻¹ *
          m j i = (K i j)⁻¹ :=
  ⟨globallyForcedWitnessMultiplier s K σ,
    globallyForcedWitnessMultiplier_equation s K hK σ⟩

end SemigenericEPPA
