import SemigenericEPPA.Valuations.PrescribedMultiplierAutomorphisms
import SemigenericEPPA.Algebra.ConstrainedWitnessMultipliers

/-!
# Genuine effective automorphism extending compatible prescribed incidence

Combine the algebraic constrained-multiplier completion with the
actual two-layer witness automorphism. The input comprises:
* an arbitrary witness-part permutation σ;
* compatible equivalences of old-label fibres ρ_q;
* a distinguished set P of witness parts;
* desired incidence multipliers a(q,r) for every q in P and r ≠ q;
* ONLY the (3.15) compatibility equations between members of P.

The output is one actual automorphism T of the full effective witness
which preserves and reflects E and every group-valued cross colour
and has exactly the prescribed target-incidence multiplier on P.
This is the bridge from (3.15)/(3.19) to (3.11)/(3.12), NOT yet the
theorem constructing a, σ, ρ from an arbitrary old partial map.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The constrained, but automatically completed, automorphism
of the actual two-layer effective witness. -/
noncomputable def prescribedEffectiveWitnessAutomorphism
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G) :
    EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D :=
  witnessAutomorphismWithMultipliers D σ ρ
    (constrainedWitnessMultiplier s K.colour σ P a)

/-- All witness-part labels follow exactly σ. -/
theorem prescribedEffectiveWitnessAutomorphism_part
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    (prescribedEffectiveWitnessAutomorphism D K σ ρ P a X).part =
      σ X.part :=
  witnessAutomorphismWithMultipliers_part D σ ρ
    (constrainedWitnessMultiplier s K.colour σ P a) X

/-- All old real labels follow their chosen fibre bijections. -/
theorem prescribedEffectiveWitnessAutomorphism_old
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    (prescribedEffectiveWitnessAutomorphism D K σ ρ P a X).old =
      (ρ X.part ⟨X.old, X.belongs⟩).val :=
  witnessAutomorphismWithMultipliers_old D σ ρ
    (constrainedWitnessMultiplier s K.colour σ P a) X

/-- On each prescribed source part, (3.11) uses the LITERALLY
prescribed multiplier a(q,r), not the canonical value 1. -/
theorem prescribedEffectiveWitnessAutomorphism_incidence
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D)
    (r : EffectiveWitnessPart D) (hr : r ≠ X.part)
    (hP : P X.part) :
    (prescribedEffectiveWitnessAutomorphism D K σ ρ P a X).crossIncidence
      (σ r) (by
        intro h
        have ht := prescribedEffectiveWitnessAutomorphism_part
          D K σ ρ P a X
        exact hr (σ.injective (h.trans ht))) =
      a X.part r * X.crossIncidence r hr := by
  calc
    (prescribedEffectiveWitnessAutomorphism D K σ ρ P a X).crossIncidence
        (σ r) (by
          intro h
          have ht := prescribedEffectiveWitnessAutomorphism_part
            D K σ ρ P a X
          exact hr (σ.injective (h.trans ht))) =
      constrainedWitnessMultiplier s K.colour σ P a X.part r *
        X.crossIncidence r hr :=
          witnessAutomorphismWithMultipliers_incidence D σ ρ
            (constrainedWitnessMultiplier s K.colour σ P a) X r hr
    _ = a X.part r * X.crossIncidence r hr := by
      rw [constrainedWitnessMultiplier_prescribed
        s K.colour σ P a X.part r hP hr.symm]

/-- Preservation and reflection of the complete E-partition. -/
theorem prescribedEffectiveWitnessAutomorphism_part_iff
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X Y : EffectiveWitnessVertex D) :
    K.toEffectiveGeometry.part
      (prescribedEffectiveWitnessAutomorphism D K σ ρ P a X)
      (prescribedEffectiveWitnessAutomorphism D K σ ρ P a Y) ↔
        K.toEffectiveGeometry.part X Y :=
  witnessAutomorphismWithMultipliers_part_iff D K σ ρ
    (constrainedWitnessMultiplier s K.colour σ P a) X Y

/-- The prescribed compatibility equations (3.15) suffice to
preserve every effective cross colour, without any additional
condition on the unconstrained edges of the witness skeleton. -/
theorem prescribedEffectiveWitnessAutomorphism_colour
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (ha : ∀ q r : EffectiveWitnessPart D,
      P q → P r → q ≠ r →
        s.normalized (a q r) * (K.colour (σ q) (σ r))⁻¹ *
          a r q = (K.colour q r)⁻¹)
    (X Y : EffectiveWitnessVertex D)
    (hXY : ¬K.toEffectiveGeometry.part X Y) :
    K.toEffectiveGeometry.F
      (prescribedEffectiveWitnessAutomorphism D K σ ρ P a X)
      (prescribedEffectiveWitnessAutomorphism D K σ ρ P a Y) =
        K.toEffectiveGeometry.F X Y :=
  witnessAutomorphismWithMultipliers_colour D K σ ρ
    (constrainedWitnessMultiplier s K.colour σ P a)
    (constrainedWitnessMultiplier_equation
      s K.colour K.reverse σ P a ha) X Y hXY

end SemigenericEPPA
