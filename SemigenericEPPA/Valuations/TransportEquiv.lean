import SemigenericEPPA.Valuations.CoordinateTransport
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Group

/-!
# Bijectivity of two-layer EPPA witness-coordinate transport

The map from CoordinateTransport satisfies equation (3.11) and uses
the TARGET part valuation. Here we prove it is a BIJECTION of the
whole two-layer witness carrier, for every witness-part permutation σ,
every family of bijections ρ_q between the corresponding old-label
fibres, and every choice of group multipliers m(q,r).

The proof factors the carrier as a dependent sum over witness parts:
  Σ q, (old-label fibre over q) × (coordinates for r ≠ q).
Each component is a genuine Equiv. The coordinate equivalence has an
explicit inverse using m(q,r)⁻¹ and the target-part valuation factor.
This avoids asserting bijectivity as an extra axiom or hypothesis.

No skeleton equation, finiteness, EPPA theorem, raw-colour hypothesis
or coherent-action hypothesis is needed for this bijection.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The permutation σ identifies the subtype of witness parts
different from q with the subtype of parts different from σq. -/
def witnessTargetEquiv
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (q : EffectiveWitnessPart D) :
    {r : EffectiveWitnessPart D // r ≠ q} ≃
      {r : EffectiveWitnessPart D // r ≠ σ q} where
  toFun r :=
    ⟨σ r.val, by
      intro h
      exact r.property (σ.injective h)⟩
  invFun r :=
    ⟨σ.symm r.val, by
      intro h
      apply r.property
      have hs := congrArg σ h
      simpa using hs⟩
  left_inv r := by
    apply Subtype.ext
    exact σ.symm_apply_apply r.val
  right_inv r := by
    apply Subtype.ext
    exact σ.apply_symm_apply r.val

/-- The unique algebraic coordinate transport is a bijection of
the two function spaces. The labels x,y may be arbitrary here;
the witness-fibre bijections will relate them in the next lemma. -/
def witnessCoordinateTransportEquiv
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (q : EffectiveWitnessPart D)
    (x y : V)
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G) :
    ({r : EffectiveWitnessPart D // r ≠ q} → G) ≃
      ({r : EffectiveWitnessPart D // r ≠ σ q} → G) := by
  let e := witnessTargetEquiv D σ q
  refine {
    toFun := fun χ target =>
      let source := e.symm target
      m q source.val * (χ source * source.val.2 x) *
        (target.val.2 y)⁻¹
    invFun := fun ψ source =>
      let target := e source
      (m q source.val)⁻¹ * (ψ target * target.val.2 y) *
        (source.val.2 x)⁻¹
    left_inv := ?_
    right_inv := ?_ }
  · intro χ
    funext source
    dsimp
    simp only [Equiv.symm_apply_apply]
    group
  · intro ψ
    funext target
    dsimp
    simp only [Equiv.apply_symm_apply]
    group

/-- The dependent fibre over witness part q, consisting of an old
vertex label in that E-class and its full vertex valuation χ. -/
abbrev EffectiveWitnessFibreData
    (D : EffectiveGeometry s V) (q : EffectiveWitnessPart D) :=
  EffectiveWitnessFibre D q ×
    ({r : EffectiveWitnessPart D // r ≠ q} → G)

/-- Each individual witness-part fibre is transported by an
equivalence: first the old vertex label moves by ρ_q, then its
valuation χ moves by the explicitly invertible coordinate equation. -/
def witnessFibreDataTransportEquiv
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (q : EffectiveWitnessPart D)
    (ρq : EffectiveWitnessFibre D q ≃
      EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G) :
    EffectiveWitnessFibreData D q ≃
      EffectiveWitnessFibreData D (σ q) where
  toFun data :=
    ⟨ρq data.1,
      (witnessCoordinateTransportEquiv D σ q
        data.1.val (ρq data.1).val m) data.2⟩
  invFun data :=
    ⟨ρq.symm data.1,
      (witnessCoordinateTransportEquiv D σ q
        (ρq.symm data.1).val data.1.val m).symm data.2⟩
  left_inv := by
    rintro ⟨x, χ⟩
    apply Prod.ext
    · exact ρq.symm_apply_apply x
    · change
        (witnessCoordinateTransportEquiv D σ q
          (ρq.symm (ρq x)).val (ρq x).val m).symm
          ((witnessCoordinateTransportEquiv D σ q
            x.val (ρq x).val m) χ) = χ
      rw [ρq.symm_apply_apply]
      exact Equiv.symm_apply_apply _ χ
  right_inv := by
    rintro ⟨y, ψ⟩
    apply Prod.ext
    · exact ρq.apply_symm_apply y
    · change
        (witnessCoordinateTransportEquiv D σ q
          (ρq.symm y).val (ρq (ρq.symm y)).val m)
          ((witnessCoordinateTransportEquiv D σ q
            (ρq.symm y).val y.val m).symm ψ) = ψ
      rw [ρq.apply_symm_apply]
      exact Equiv.apply_symm_apply _ ψ

/-- A witness vertex is exactly a dependent sum of its part label,
old vertex fibre and valuation function. This is an equivalence of
actual data, not an encoding with forgotten membership information. -/
def witnessVertexSigmaEquiv (D : EffectiveGeometry s V) :
    EffectiveWitnessVertex D ≃
      (Σ q : EffectiveWitnessPart D,
        EffectiveWitnessFibreData D q) where
  toFun X := ⟨X.part, ⟨⟨X.old, X.belongs⟩, X.vertexValuation⟩⟩
  invFun X := {
    part := X.1
    old := X.2.1.val
    belongs := X.2.1.property
    vertexValuation := X.2.2 }
  left_inv := by
    intro X
    cases X
    rfl
  right_inv := by
    rintro ⟨q, ⟨⟨x, hx⟩, χ⟩⟩
    rfl

/-- The total witness vertex transport is a genuine bijection.
The coordinate transport is built from independent invertible maps
on each part fibre and the permutation σ of the part labels. -/
def witnessVertexTransportEquiv
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G) :
    EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D :=
  (witnessVertexSigmaEquiv D).trans
    ((Equiv.sigmaCongr σ (fun q =>
      witnessFibreDataTransportEquiv D σ q (ρ q) m)).trans
       (witnessVertexSigmaEquiv D).symm)

/-- The bijection defined above is exactly the earlier explicit
coordinate-transport map, whose target-incidence identity has already
been verified as equation (3.11). -/
theorem witnessVertexTransportEquiv_apply
    (D : EffectiveGeometry s V)
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (X : EffectiveWitnessVertex D) :
    witnessVertexTransportEquiv D σ ρ m X =
      transportWitnessVertex D σ ρ m X := by
  cases X
  rfl

end SemigenericEPPA
