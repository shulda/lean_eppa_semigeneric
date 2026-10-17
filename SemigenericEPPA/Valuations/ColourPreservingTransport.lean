import SemigenericEPPA.Valuations.CoordinateTransport
import SemigenericEPPA.Algebra.SkeletonMultipliers

/-!
# Witness-coordinate transport preserves the effective geometry

The explicit map from CoordinateTransport.lean sends a valuation witness
vertex X=(q,x,χ) to a vertex over σ(q), using a prescribed bijection
of old labels in the corresponding E-classes and the exact equation

  λ_(ΘX)(σr) = m(q,r) λ_X(r).                            (3.11)

If the ordered multipliers satisfy the affine skeleton law (3.9),
the map preserves AND reflects E and preserves EVERY effective cross
colour (3.6). The noncommutative cancellation is exactly (3.12).

This is the full effective-colour correctness theorem for a candidate
valuation-witness automorphism. Its bijectivity and actual existence
for each old partial automorphism are separate proof obligations.
There are no finiteness, S-saturation or HKN assumptions.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Any part permutation, fibrewise bijections and ordered multiplier
family define a candidate map of witness vertices. -/
theorem transportWitnessVertex_part_iff
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X Y : EffectiveWitnessVertex D) :
    K.toEffectiveGeometry.part
        (transportWitnessVertex D σ ρ m X)
        (transportWitnessVertex D σ ρ m Y) ↔
      K.toEffectiveGeometry.part X Y := by
  change σ X.part = σ Y.part ↔ X.part = Y.part
  constructor
  · intro heq
    exact σ.injective heq
  · intro heq
    exact congrArg σ heq

/-- In the precise noncommutative order of manuscript (3.12),
the transported candidate preserves the effective colour between
every two distinct witness parts. -/
theorem transportWitnessVertex_preserves_crossColour
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
    (hXY : X.part ≠ Y.part) :
    K.toEffectiveGeometry.F
      (transportWitnessVertex D σ ρ m X)
      (transportWitnessVertex D σ ρ m Y) =
        K.toEffectiveGeometry.F X Y := by
  let T := transportWitnessVertex D σ ρ m
  have hnew : (T X).part ≠ (T Y).part := by
    change σ X.part ≠ σ Y.part
    intro heq
    exact hXY (σ.injective heq)
  have htx :
      (T X).crossIncidence (T Y).part hnew.symm =
        m X.part Y.part * X.crossIncidence Y.part hXY.symm := by
    exact transportWitnessVertex_crossIncidence
      D σ ρ m X Y.part hXY.symm
  have hty :
      (T Y).crossIncidence (T X).part hnew =
        m Y.part X.part * Y.crossIncidence X.part hXY := by
    exact transportWitnessVertex_crossIncidence
      D σ ρ m Y X.part hXY
  calc
    K.toEffectiveGeometry.F (T X) (T Y) =
        gaugeColour s
          ((T X).crossIncidence (T Y).part hnew.symm)
          (K.colour (T X).part (T Y).part)
          ((T Y).crossIncidence (T X).part hnew) :=
      K.witness_cross_colour (T X) (T Y) hnew
    _ = gaugeColour s
          (m X.part Y.part * X.crossIncidence Y.part hXY.symm)
          (K.colour (σ X.part) (σ Y.part))
          (m Y.part X.part * Y.crossIncidence X.part hXY) := by
      rw [htx, hty]
      rfl
    _ = gaugeColour s
          (X.crossIncidence Y.part hXY.symm)
          (K.colour X.part Y.part)
          (Y.crossIncidence X.part hXY) :=
      eppe_multiplier_preserves_gaugeColour
        s (K.colour X.part Y.part)
          (K.colour (σ X.part) (σ Y.part))
          (m X.part Y.part) (m Y.part X.part)
          (X.crossIncidence Y.part hXY.symm)
          (Y.crossIncidence X.part hXY)
          (hm X.part Y.part hXY)
    _ = K.toEffectiveGeometry.F X Y :=
      (K.witness_cross_colour X Y hXY).symm

/-- Packaging the candidate automorphism's two mathematically
essential preservation properties; bijectivity is a distinct gate. -/
theorem transportWitnessVertex_preserves_effective
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (hm : ∀ q r : EffectiveWitnessPart D, q ≠ r →
      s.normalized (m q r) * (K.colour (σ q) (σ r))⁻¹ *
        m r q = (K.colour q r)⁻¹) :
    (∀ X Y : EffectiveWitnessVertex D,
      K.toEffectiveGeometry.part
        (transportWitnessVertex D σ ρ m X)
        (transportWitnessVertex D σ ρ m Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
    (∀ X Y : EffectiveWitnessVertex D,
      ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F
          (transportWitnessVertex D σ ρ m X)
          (transportWitnessVertex D σ ρ m Y) =
        K.toEffectiveGeometry.F X Y) := by
  constructor
  · exact transportWitnessVertex_part_iff D K σ ρ m
  · intro X Y h
    exact transportWitnessVertex_preserves_crossColour
      D K σ ρ m hm X Y h

end SemigenericEPPA
