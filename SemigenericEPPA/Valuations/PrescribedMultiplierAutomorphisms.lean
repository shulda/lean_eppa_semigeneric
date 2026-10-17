import SemigenericEPPA.Valuations.TwistedPartPermutation

/-!
# Effective-witness automorphisms with prescribed multipliers

The canonical choice of all pair multipliers in EffectiveAutomorphisms
is sufficient to produce an automorphism, but NOT sufficient to
extend an arbitrary prescribed old partial automorphism: manuscript
(3.14), (3.15) and (3.19) prescribe multipliers on certain pairs.

This module therefore packages the more general statement. Any family
m(q,r) satisfying the exact noncommutative affine skeleton equation
(3.9) yields a genuine automorphism, with EXACT real-label and
target-incidence formulas (3.11). In particular m need not be the
canonical globally forced choice; it can be a constrained completion.

The choice of m from the old partial automorphism and the proof that
all prescribed equations are compatible remain open E0 gates.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- A genuine total permutation of the witness vertices for *any*
chosen ordered-pair multipliers. The skeleton condition is needed
only for its automorphism property, not for bijectivity. -/
def witnessAutomorphismWithMultipliers
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G) :
    EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D :=
  witnessVertexTransportEquiv D σ ρ m

theorem witnessAutomorphismWithMultipliers_part
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    (witnessAutomorphismWithMultipliers D σ ρ m X).part =
      σ X.part := by
  rw [witnessAutomorphismWithMultipliers,
    witnessVertexTransportEquiv_apply, transportWitnessVertex_part]

/-- On every witness vertex, the old label moves by the explicitly
chosen fibre bijection. -/
theorem witnessAutomorphismWithMultipliers_old
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    (witnessAutomorphismWithMultipliers D σ ρ m X).old =
      (ρ X.part ⟨X.old, X.belongs⟩).val := by
  rw [witnessAutomorphismWithMultipliers,
    witnessVertexTransportEquiv_apply, transportWitnessVertex_old]

/-- Equation (3.11), unchanged when the pair multipliers are
constrained rather than chosen by a global auxiliary linear order. -/
theorem witnessAutomorphismWithMultipliers_incidence
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D)
    (r : EffectiveWitnessPart D) (hr : r ≠ X.part) :
    (witnessAutomorphismWithMultipliers D σ ρ m X).crossIncidence
      (σ r) (by
        intro h
        exact hr (σ.injective h)) =
      m X.part r * X.crossIncidence r hr := by
  simpa only [witnessAutomorphismWithMultipliers,
    witnessVertexTransportEquiv_apply] using
      (transportWitnessVertex_crossIncidence D σ ρ m X r hr)

/-- Exact E preservation and reflection for an arbitrary selected
multiplier family. -/
theorem witnessAutomorphismWithMultipliers_part_iff
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X Y : EffectiveWitnessVertex D) :
    K.toEffectiveGeometry.part
      (witnessAutomorphismWithMultipliers D σ ρ m X)
      (witnessAutomorphismWithMultipliers D σ ρ m Y) ↔
        K.toEffectiveGeometry.part X Y := by
  simpa only [witnessAutomorphismWithMultipliers,
    witnessVertexTransportEquiv_apply] using
      (transportWitnessVertex_part_iff D K σ ρ m X Y)

/-- The genuine witness permutation preserves every effective group
colour provided precisely the skeleton equations (3.9) hold. -/
theorem witnessAutomorphismWithMultipliers_colour
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hm : ∀ q r : EffectiveWitnessPart D, q ≠ r →
      s.normalized (m q r) * (K.colour (σ q) (σ r))⁻¹ *
        m r q = (K.colour q r)⁻¹)
    (X Y : EffectiveWitnessVertex D)
    (hXY : ¬K.toEffectiveGeometry.part X Y) :
    K.toEffectiveGeometry.F
      (witnessAutomorphismWithMultipliers D σ ρ m X)
      (witnessAutomorphismWithMultipliers D σ ρ m Y) =
        K.toEffectiveGeometry.F X Y := by
  have hparts : X.part ≠ Y.part := by
    intro heq
    exact hXY ((K.witness_part_iff X Y).2 heq)
  simpa only [witnessAutomorphismWithMultipliers,
    witnessVertexTransportEquiv_apply] using
      (transportWitnessVertex_preserves_crossColour
        D K σ ρ m hm X Y hparts)

/-- The precise existence interface for arbitrary compatible m.
Unlike the canonical automorphism theorem, this accepts prescribed
multipliers on a chosen collection of witness-part pairs. -/
theorem exists_witnessAutomorphismWithMultipliers
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hm : ∀ q r : EffectiveWitnessPart D, q ≠ r →
      s.normalized (m q r) * (K.colour (σ q) (σ r))⁻¹ *
        m r q = (K.colour q r)⁻¹) :
    ∃ T : EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D,
      (∀ X, (T X).part = σ X.part) ∧
      (∀ X Y,
        K.toEffectiveGeometry.part (T X) (T Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ X Y, ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F (T X) (T Y) =
          K.toEffectiveGeometry.F X Y) := by
  refine ⟨witnessAutomorphismWithMultipliers D σ ρ m, ?_, ?_, ?_⟩
  · exact witnessAutomorphismWithMultipliers_part D σ ρ m
  · exact witnessAutomorphismWithMultipliers_part_iff D K σ ρ m
  · exact witnessAutomorphismWithMultipliers_colour D K σ ρ m hm

end SemigenericEPPA
