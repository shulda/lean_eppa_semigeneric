import SemigenericEPPA.Algebra.GlobalWitnessMultipliers
import SemigenericEPPA.Valuations.ColourPreservingTransport
import SemigenericEPPA.Valuations.TransportEquiv
import Mathlib.Order.Basic

/-!
# Actual automorphisms of the two-layer effective witness

We now combine four separately verified construction gates:
* Every permutation σ of witness parts has a globally compatible
  multiplier family m(q,r) satisfying the AFFINE skeleton law (3.9).
* For every q, an arbitrary bijection ρ_q of old-label fibres and
  this multiplier family define the transport of valuations (3.11).
* The transport is an actual BIJECTION of the full witness vertex sort.
* The affine skeleton equation makes the transport preserve the
  effective cross-colours (3.12), and it preserves/refects E.

The result is a concrete equivalence of witness vertices which is an
automorphism of the entire effective group-valued rectangle geometry.
There is no HKN black box or automorphism-existence axiom.

The remaining EPPA problem is to choose σ and ρ_q in such a way that
the resulting automorphism EXTENDS any requested old partial
automorphism. The theorem below does not assert that step.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- A concrete total effective-witness automorphism candidate.
The auxiliary linear order only picks the skeleton multipliers;
it does NOT become part of the effective relational structure. -/
noncomputable def effectiveWitnessAutomorphism
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q)) :
    EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D :=
  witnessVertexTransportEquiv D σ ρ
    (globallyForcedWitnessMultiplier s K.colour σ)

/-- The automorphism sends every witness vertex over q to the
part σ(q), exactly as required in equation (3.11). -/
theorem effectiveWitnessAutomorphism_part
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (X : EffectiveWitnessVertex D) :
    (effectiveWitnessAutomorphism D K σ ρ X).part = σ X.part := by
  change (witnessVertexTransportEquiv D σ ρ
    (globallyForcedWitnessMultiplier s K.colour σ) X).part = σ X.part
  rw [witnessVertexTransportEquiv_apply]
  rfl

/-- Preservation AND reflection of the effective E-relation by
the actual witness-vertex bijection. -/
theorem effectiveWitnessAutomorphism_part_iff
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (X Y : EffectiveWitnessVertex D) :
    K.toEffectiveGeometry.part
      (effectiveWitnessAutomorphism D K σ ρ X)
      (effectiveWitnessAutomorphism D K σ ρ Y) ↔
        K.toEffectiveGeometry.part X Y := by
  simpa only [effectiveWitnessAutomorphism,
    witnessVertexTransportEquiv_apply] using
    (transportWitnessVertex_part_iff D K σ ρ
      (globallyForcedWitnessMultiplier s K.colour σ) X Y)

/-- Preservation of EVERY cross-part effective colour in the
noncommutative and genuinely affine setting, with the bijectivity
of the witness automorphism already established. -/
theorem effectiveWitnessAutomorphism_colour
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (X Y : EffectiveWitnessVertex D)
    (hXY : ¬K.toEffectiveGeometry.part X Y) :
    K.toEffectiveGeometry.F
      (effectiveWitnessAutomorphism D K σ ρ X)
      (effectiveWitnessAutomorphism D K σ ρ Y) =
        K.toEffectiveGeometry.F X Y := by
  have hparts : X.part ≠ Y.part := by
    intro heq
    exact hXY ((K.witness_part_iff X Y).2 heq)
  have hm :=
    globallyForcedWitnessMultiplier_equation
      s K.colour K.reverse σ
  simpa only [effectiveWitnessAutomorphism,
    witnessVertexTransportEquiv_apply] using
    (transportWitnessVertex_preserves_crossColour
      D K σ ρ (globallyForcedWitnessMultiplier s K.colour σ)
      hm X Y hparts)

/-- For ANY witness-part permutation admitting per-part old-label
bijections, there exists an effective-witness automorphism, not
merely a colour-preserving candidate function.

The value returned is a genuine Equiv of the full two-layer
witness-vertex sort, and both the exact E relation and every
effective cross-part colour are preserved. -/
theorem exists_effectiveWitnessAutomorphism
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q)) :
    ∃ T : EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D,
      (∀ X, (T X).part = σ X.part) ∧
      (∀ X Y, K.toEffectiveGeometry.part (T X) (T Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ X Y, ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (T X) (T Y) =
            K.toEffectiveGeometry.F X Y) := by
  refine ⟨effectiveWitnessAutomorphism D K σ ρ, ?_, ?_, ?_⟩
  · intro X
    exact effectiveWitnessAutomorphism_part D K σ ρ X
  · intro X Y
    exact effectiveWitnessAutomorphism_part_iff D K σ ρ X Y
  · intro X Y hXY
    exact effectiveWitnessAutomorphism_colour D K σ ρ X Y hXY

end SemigenericEPPA
