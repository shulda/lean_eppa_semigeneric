import SemigenericEPPA.Algebra.GlobalWitnessMultipliers

/-!
# Completing prescribed witness multipliers (3.15), (3.19)

The old partial automorphism determines a family a(q,r) for every
ordered pair with source q in a distinguished subset P of witness
parts. On pairs with BOTH endpoints in P, manuscript equation (3.15)
is the compatibility condition. On all remaining pairs the reverse
multiplier is uniquely forced by the affine skeleton condition (3.9).

This module constructs one global m respecting EVERY prescribed
outgoing multiplier and satisfying (3.9) in both orientations.
The proof works for a noncommutative group with affine reversal;
the only additional choice is an auxiliary linear order on the
unconstrained pairs. There is no EPPA or raw-cover assumption.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G]
variable {I : Type v} [LinearOrder I]

/-- If i belongs to P, preserve a(i,j); if only j belongs to P,
use the algebraically forced reverse of a(j,i); if neither endpoint
is prescribed, use the verified global order-based choice.
Diagonal values are irrelevant to the skeleton equation. -/
noncomputable def constrainedWitnessMultiplier
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (σ : I ≃ I)
    (P : I → Prop)
    (a : I → I → G)
    (i j : I) : G := by
  classical
  exact if i = j then 1
    else if P i then a i j
    else if P j then
      eppeReverseMultiplier s (K j i) (K (σ j) (σ i)) (a j i)
    else globallyForcedWitnessMultiplier s K σ i j

/-- All prescribed outgoing multipliers are retained literally,
provided the endpoints differ. -/
theorem constrainedWitnessMultiplier_prescribed
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (σ : I ≃ I)
    (P : I → Prop)
    (a : I → I → G)
    (i j : I)
    (hi : P i) (hij : i ≠ j) :
    constrainedWitnessMultiplier s K σ P a i j = a i j := by
  simp [constrainedWitnessMultiplier, hij, hi]

@[simp] theorem constrainedWitnessMultiplier_diag
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (σ : I ≃ I)
    (P : I → Prop)
    (a : I → I → G)
    (i : I) :
    constrainedWitnessMultiplier s K σ P a i i = 1 := by
  simp [constrainedWitnessMultiplier]

/-- The prescribed multiplier equations on P × P are the ONLY
compatibility assumption. They suffice to complete all other pairs
with the exact affine/noncommutative skeleton equation (3.9). -/
theorem constrainedWitnessMultiplier_equation
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (hK : ∀ i j : I, i ≠ j → K j i = s (K i j))
    (σ : I ≃ I)
    (P : I → Prop)
    (a : I → I → G)
    (ha : ∀ i j : I, P i → P j → i ≠ j →
      s.normalized (a i j) * (K (σ i) (σ j))⁻¹ *
        a j i = (K i j)⁻¹)
    (i j : I) (hij : i ≠ j) :
    s.normalized (constrainedWitnessMultiplier s K σ P a i j) *
        (K (σ i) (σ j))⁻¹ *
          constrainedWitnessMultiplier s K σ P a j i =
      (K i j)⁻¹ := by
  classical
  by_cases hi : P i
  · by_cases hj : P j
    · simpa [constrainedWitnessMultiplier, hij, hij.symm, hi, hj] using
        ha i j hi hj hij
    · have hf := eppe_reverseMultiplier_forward s
        (K i j) (K (σ i) (σ j)) (a i j)
      simpa [constrainedWitnessMultiplier, hij, hij.symm, hi, hj] using hf
  · by_cases hj : P j
    · have hk : K i j = s (K j i) := hK j i hij.symm
      have hsk : K (σ i) (σ j) =
          s (K (σ j) (σ i)) := by
        apply hK (σ j) (σ i)
        intro h
        exact hij.symm (σ.injective h)
      have hb := eppe_reverseMultiplier_backward s
        (K j i) (K (σ j) (σ i)) (a j i)
      simpa [constrainedWitnessMultiplier, hij, hij.symm,
        hi, hj, hk, hsk] using hb
    · have hg := globallyForcedWitnessMultiplier_equation
        s K hK σ i j hij
      simpa [constrainedWitnessMultiplier, hij, hij.symm, hi, hj] using hg

/-- Packaged existence theorem with both the prescribed values
and the global affine skeleton law. This is the algebraic completion
step needed between manuscript equations (3.15) and (3.19). -/
theorem exists_constrainedWitnessMultipliers
    (s : AffineAntiInvolution G)
    (K : I → I → G)
    (hK : ∀ i j : I, i ≠ j → K j i = s (K i j))
    (σ : I ≃ I)
    (P : I → Prop)
    (a : I → I → G)
    (ha : ∀ i j : I, P i → P j → i ≠ j →
      s.normalized (a i j) * (K (σ i) (σ j))⁻¹ *
        a j i = (K i j)⁻¹) :
    ∃ m : I → I → G,
      (∀ i j : I, P i → i ≠ j → m i j = a i j) ∧
      (∀ i j : I, i ≠ j →
        s.normalized (m i j) * (K (σ i) (σ j))⁻¹ *
          m j i = (K i j)⁻¹) := by
  refine ⟨constrainedWitnessMultiplier s K σ P a, ?_, ?_⟩
  · intro i j hi hij
    exact constrainedWitnessMultiplier_prescribed s K σ P a i j hi hij
  · exact constrainedWitnessMultiplier_equation s K hK σ P a ha

end SemigenericEPPA
