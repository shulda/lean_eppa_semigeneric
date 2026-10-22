import SemigenericEPPA.Valuations.NeutralMultiplierCompatibility
import SemigenericEPPA.Valuations.OldVertexExtensionCriterion
import SemigenericEPPA.Valuations.GaugeOldEffectiveEmbedding

/-!
# Fixed indexed-gauge compatibility and literal gauge-old vertex extension

The coherent nontrivial-G construction uses ONE prechosen indexed
gauge P and embeds old labels as D.gaugeOldWitnessVertex
P.vertexGauge. The original ordinary EPPA partial-map lemmas
worked instead with the canonical quotient gauge and the
canonical D.oldWitnessVertex.

We separate two generic bridges needed to reuse the existing
strict witness-automorphism machinery without ever changing the
chosen fixed good skeleton:
1. If K equals P.skeleton on the distinguished neutral parts,
   the (3.15) partial gauge multiplier equation for P implies
   the exact prescribed witness-part compatibility (3.9).
2. The general prescribed valuation automorphism extends a
   given literal gauge-old vertex whenever its part, real label
   and all incidence coordinates are the requested ones.

These are entirely algebraic and extensional facts, valid for
noncommutative G and an arbitrary affine anti-involution.
Individual connectors are NOT yet asserted.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Compatibility of visited neutral-part multipliers with the
globally fixed indexed-gauge skeleton rather than the canonical
quotient-gauge skeleton. -/
theorem neutralPrescribedMultiplier_compatible_onIndexedGauge
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (P : IndexedGauge s V (Quotient D.part))
    (hK : ∀ i j : Quotient D.part, i ≠ j →
      K.colour (distinguishedWitnessPart D i)
        (distinguishedWitnessPart D j) = P.skeleton i j)
    (iota : Equiv.Perm (Quotient D.part))
    (pi : Equiv.Perm V)
    (L : Quotient D.part → V → G)
    (visited : Quotient D.part → Prop)
    (hL : ∀ j, visited j → ∀ x, L j x = 1)
    (m : Quotient D.part → Quotient D.part → G)
    (hm : ∀ i j, visited i → visited j → i ≠ j →
      s.normalized (m i j) *
          (P.skeleton (iota i) (iota j))⁻¹ * m j i =
        (P.skeleton i j)⁻¹)
    (q r : EffectiveWitnessPart D)
    (hq : IsVisitedNeutralPart D visited q)
    (hr : IsVisitedNeutralPart D visited r)
    (hqr : q ≠ r) :
    s.normalized (neutralPrescribedMultiplier D m q r) *
        (K.colour
          (twistedWitnessPartPerm D iota pi L q)
          (twistedWitnessPartPerm D iota pi L r))⁻¹ *
          neutralPrescribedMultiplier D m r q =
      (K.colour q r)⁻¹ := by
  have hij : q.1 ≠ r.1 := by
    intro heq
    apply hqr
    apply Prod.ext
    · exact heq
    · exact hq.2.trans hr.2.symm
  have hqe : q = distinguishedWitnessPart D q.1 := by
    apply Prod.ext
    · rfl
    · exact hq.2
  have hre : r = distinguishedWitnessPart D r.1 := by
    apply Prod.ext
    · rfl
    · exact hr.2
  have hsq :
      twistedWitnessPartPerm D iota pi L q =
        distinguishedWitnessPart D (iota q.1) := by
    conv_lhs => rw [hqe]
    exact twistedWitnessPartPerm_distinguished
      D iota pi L q.1 (hL q.1 hq.1)
  have hsr :
      twistedWitnessPartPerm D iota pi L r =
        distinguishedWitnessPart D (iota r.1) := by
    conv_lhs => rw [hre]
    exact twistedWitnessPartPerm_distinguished
      D iota pi L r.1 (hL r.1 hr.1)
  have hKold :
      K.colour q r = P.skeleton q.1 r.1 := by
    rw [hqe, hre]
    exact hK q.1 r.1 hij
  have hKnew :
      K.colour
          (twistedWitnessPartPerm D iota pi L q)
          (twistedWitnessPartPerm D iota pi L r) =
        P.skeleton (iota q.1) (iota r.1) := by
    rw [hsq, hsr]
    exact hK (iota q.1) (iota r.1) (by
      intro h
      exact hij (iota.injective h))
  change s.normalized (m q.1 r.1) *
      (K.colour
        (twistedWitnessPartPerm D iota pi L q)
        (twistedWitnessPartPerm D iota pi L r))⁻¹ *
        m r.1 q.1 = (K.colour q r)⁻¹
  rw [hKnew, hKold]
  exact hm q.1 r.1 hq.1 hr.1 hij

/-- Pointwise extension criterion for the literal old embedding
from an arbitrary fixed gauge row matrix. It is independent of
the chosen canonical quotient-gauge old embedding. -/
theorem prescribedEffectiveWitnessAutomorphism_maps_gaugeOld
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (a : V → Quotient D.part → G)
    (sigma : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (rho : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (sigma q))
    (P : EffectiveWitnessPart D → Prop)
    (m : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (x y : V)
    (hP : P (oldWitnessPart D x))
    (hpart : sigma (oldWitnessPart D x) = oldWitnessPart D y)
    (hold : (rho (oldWitnessPart D x) ⟨x, rfl⟩).val = y)
    (hinc : ∀ (r : EffectiveWitnessPart D)
        (hr : r ≠ oldWitnessPart D x),
      m (oldWitnessPart D x) r *
          (D.gaugeOldWitnessVertex a x).crossIncidence r hr =
        (D.gaugeOldWitnessVertex a y).crossIncidence
          (sigma r) (by
            intro heq
            apply hr
            apply sigma.injective
            exact heq.trans hpart.symm)) :
    prescribedEffectiveWitnessAutomorphism D K sigma rho P m
      (D.gaugeOldWitnessVertex a x) =
        D.gaugeOldWitnessVertex a y := by
  let X := D.gaugeOldWitnessVertex a x
  let Y := D.gaugeOldWitnessVertex a y
  let T := prescribedEffectiveWitnessAutomorphism D K sigma rho P m
  apply EffectiveWitnessVertex.eq_of_crossIncidence (T X) Y
  · exact (prescribedEffectiveWitnessAutomorphism_part
      D K sigma rho P m X).trans hpart
  · exact (prescribedEffectiveWitnessAutomorphism_old
      D K sigma rho P m X).trans hold
  · intro r hrT hrY
    let u : EffectiveWitnessPart D := sigma.symm r
    have hu : u ≠ X.part := by
      intro heq
      apply hrT
      calc
        r = sigma u := (sigma.apply_symm_apply r).symm
        _ = sigma X.part := congrArg sigma heq
        _ = (T X).part :=
          (prescribedEffectiveWitnessAutomorphism_part
            D K sigma rho P m X).symm
    have htransport :=
      prescribedEffectiveWitnessAutomorphism_incidence
        D K sigma rho P m X u hu hP
    have htarget := hinc u hu
    have hresult := htransport.trans htarget
    simpa only [u, Equiv.apply_symm_apply, T, X, Y] using hresult

end SemigenericEPPA
