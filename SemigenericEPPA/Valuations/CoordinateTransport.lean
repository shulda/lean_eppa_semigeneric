import SemigenericEPPA.Valuations.EffectiveCarrier
import Mathlib.Tactic.Group

/-!
# The exact coordinate transport equation (3.11)

An effective EPPA witness vertex is (q,x,χ). Its incidence coordinate
towards a target witness part r=(j,g) is

  λ_X(r) = χ(r) * g(x),

using the valuation of the TARGET part, never that of the source part.
When witness parts are permuted by σ and the old point labels move
along bijections of the corresponding old E-classes, the required
incidence transformation is

  λ_(ΘX)(σr) = m(q,r) * λ_X(r).

This file constructs the transported witness vertex explicitly.
Its new raw χ-coordinate is obtained by cancelling the TARGET part
valuation at the new old label. It also proves this coordinate is
uniquely forced by the incidence equation. Finiteness, skeleton
equivariance and automorphism existence are independent later gates.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The old real vertices belonging to witness part q. Each q
contains the old E-class q.1, independent of its part valuation. -/
abbrev EffectiveWitnessFibre (D : EffectiveGeometry s V)
    (q : EffectiveWitnessPart D) :=
  {x : V // Quotient.mk D.part x = q.1}

/-- The transported vertex valuation χ' is forced by the incidence
equation χ'(σr)·(σr).2(y) = m(q,r)·χ(r)·r.2(x).
The new old vertex y lies in the class of σq, provided by ρ. -/
def transportWitnessVertex
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    EffectiveWitnessVertex D := by
  let y : EffectiveWitnessFibre D (σ X.part) :=
    ρ X.part ⟨X.old, X.belongs⟩
  refine {
    part := σ X.part
    old := y.val
    belongs := y.property
    vertexValuation := ?_ }
  intro r
  let oldTarget := σ.symm r.val
  have hdiff : oldTarget ≠ X.part := by
    intro heq
    apply r.property
    have h := congrArg σ heq
    simpa [oldTarget] using h
  exact m X.part oldTarget *
      X.crossIncidence oldTarget hdiff *
      (r.val.2 y.val)⁻¹

@[simp] theorem transportWitnessVertex_part
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    (transportWitnessVertex D σ ρ m X).part = σ X.part := rfl

@[simp] theorem transportWitnessVertex_old
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    (transportWitnessVertex D σ ρ m X).old =
      (ρ X.part ⟨X.old, X.belongs⟩).val := rfl

/-- The exact target-part incidence identity (3.11), which will
supply the coordinate equation for the witness automorphism. -/
theorem transportWitnessVertex_crossIncidence
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D)
    (r : EffectiveWitnessPart D) (hr : r ≠ X.part) :
    (transportWitnessVertex D σ ρ m X).crossIncidence
        (σ r) (by
          intro heq
          exact hr (σ.injective heq)) =
      m X.part r * X.crossIncidence r hr := by
  unfold EffectiveWitnessVertex.crossIncidence
  dsimp [transportWitnessVertex]
  simp only [Equiv.symm_apply_apply]
  group

/-- The transported χ-coordinate is the UNIQUE solution to the
incidence equation, since the target-part valuation is invertible.
This guarantees that valuation transport cannot introduce hidden
degrees of freedom. -/
theorem witnessCoordinate_eq_iff
    (m oldInc targetVal candidate : G) :
    candidate * targetVal = m * oldInc ↔
      candidate = m * oldInc * targetVal⁻¹ := by
  constructor
  · intro h
    calc
      candidate = (candidate * targetVal) * targetVal⁻¹ := by group
      _ = (m * oldInc) * targetVal⁻¹ := by rw [h]
      _ = m * oldInc * targetVal⁻¹ := by group
  · intro h
    rw [h]
    group

end SemigenericEPPA
