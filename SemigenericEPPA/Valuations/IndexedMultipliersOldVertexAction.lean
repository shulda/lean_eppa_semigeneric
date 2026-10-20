import SemigenericEPPA.Valuations.IndexedMultipliersWitnessHAction
import SemigenericEPPA.Valuations.OldVertexExtensionCriterion
import Mathlib.Tactic.Group

/-!
# Actual old-vertex extension for index-based valuation H-actions

An index-pair multiplier cocycle can be pulled back to all two-layer
witness parts and gives a genuine group action. For coherent EPPA we
must additionally check the LITERAL old vertex, not merely its part or
underlying old real label.

Use the untwisted reference z=1 and suppose the multiplier transports
the complete old quotient-gauge row, INCLUDING the diagonal entry.
Then the full target-part incidence coordinates of the distinguished
old witnesses transform exactly, and the genuine group action maps
  oldWitnessVertex(x) -> oldWitnessVertex(rho(h)(x)).

The diagonal row equation is intentionally explicit: the dummy
same-E quotient gauge coordinate can otherwise vary under rho,
and different blown-up witness parts with equal old class index
really do exist. Cross-part effective invariance alone does not
justify that equation. No blanket coherent EPPA theorem is asserted.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- One canonical full two-layer group action using z=1 and an
old-class-index multiplier cocycle. It is determined only by the
original data, without choosing a different lift for each h. -/
noncomputable def indexedWitnessAction
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j) :
    H →* Equiv.Perm (EffectiveWitnessVertex D) :=
  referenceWitnessCocycleAction D rho iota (fun _ _ => (1 : G)) hcls
    (fun h q r => M h q.1 r.1)
    (by intro q r _; exact hOne q.1 r.1)
    (by
      intro k h q r _
      change M (k * h) q.1 r.1 =
        M k
          (referenceWitnessPartAction D rho iota (fun _ _ => (1 : G))
            h q).1
          (referenceWitnessPartAction D rho iota (fun _ _ => (1 : G))
            h r).1 * M h q.1 r.1
      rw [referenceWitnessPartAction_class D rho iota
        (fun _ _ => (1 : G)) h q,
        referenceWitnessPartAction_class D rho iota
        (fun _ _ => (1 : G)) h r]
      exact hMul k h q.1 r.1)

/-- With its multipliers transporting the actual COMPLETE canonical
quotient-gauge row of the original geometry, the constructed full
valuation H-action extends the old H-action exactly on every old
valuation vertex, not just on labels or class indices.

The diagonal gauge equation is essential and is NOT inferred from
cross-part E/F-invariance without further normalization. -/
theorem indexedWitnessAction_maps_old
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (hRow : ∀ (h : H) (x : V) (j : Quotient D.part),
      M h (Quotient.mk D.part x) j *
        D.toQuotientGauge.vertexGauge x j =
          D.toQuotientGauge.vertexGauge (rho h x) (iota h j))
    (h : H) (x : V) :
    D.indexedWitnessAction rho iota hcls M hOne hMul h
      (D.oldWitnessVertex x) =
        D.oldWitnessVertex (rho h x) := by
  let z : V → Quotient D.part → G := fun _ _ => 1
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  let m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G :=
    fun h q r => M h q.1 r.1
  let T : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.indexedWitnessAction rho iota hcls M hOne hMul
  let X : EffectiveWitnessVertex D := D.oldWitnessVertex x
  let Y : EffectiveWitnessVertex D := D.oldWitnessVertex (rho h x)
  have hNeutral (j : Quotient D.part) :
      sigma h (distinguishedWitnessPart D j) =
        distinguishedWitnessPart D (iota h j) :=
    referenceWitnessPartAction_neutral D rho iota z h j (by intro y; rfl)
  have hSigmaVal (r : EffectiveWitnessPart D) :
      (sigma h r).2 (rho h x) = r.2 x := by
    change
      (twistedWitnessPartPerm D (iota h) (rho h)
        (fun j y => referenceGaugeTwist rho iota z h y j) r).2
        (rho h x) = r.2 x
    rw [twistedWitnessPartPerm_valuation]
    simp [z, referenceGaugeTwist]
  have hpart : (T h X).part = Y.part := by
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).part = Y.part
    rw [witnessCocyclePerm_part]
    change sigma h (oldWitnessPart D x) =
      oldWitnessPart D (rho h x)
    calc
      sigma h (oldWitnessPart D x) =
        distinguishedWitnessPart D (iota h (Quotient.mk D.part x)) :=
          hNeutral (Quotient.mk D.part x)
      _ = oldWitnessPart D (rho h x) := by
        rw [← hcls h x]
        rfl
  have hold : (T h X).old = Y.old := by
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).old = rho h x
    exact witnessCocyclePerm_old D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X
  apply EffectiveWitnessVertex.eq_of_crossIncidence (T h X) Y
    hpart hold
  intro r hrT hrY
  let u : EffectiveWitnessPart D := (sigma h).symm r
  have hu : u ≠ X.part := by
    intro heq
    apply hrT
    calc
      r = sigma h u := ((sigma h).apply_symm_apply r).symm
      _ = sigma h X.part := congrArg (sigma h) heq
      _ = (T h X).part := by
        change sigma h X.part = (T h X).part
        exact (witnessCocyclePerm_part D sigma rho
          (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
          m h X).symm
  have htransport :
      (T h X).crossIncidence (sigma h u) (by
        intro heq
        exact hu ((sigma h).injective
          (heq.trans (by
            change (T h X).part = sigma h X.part
            exact (witnessCocyclePerm_part D sigma rho
              (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
              m h X).symm))) =
        m h X.part u * X.crossIncidence u hu :=
    witnessCocyclePerm_incidence D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X u hu
  have htarget : Y.crossIncidence (sigma h u) (by
      intro heq
      apply hu
      apply (sigma h).injective
      calc
        sigma h u = Y.part := heq
        _ = sigma h X.part := hpart.symm.trans
          (witnessCocyclePerm_part D sigma rho
            (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
            m h X)) =
        m h X.part u * X.crossIncidence u hu := by
    have hClass : (sigma h u).1 = iota h u.1 :=
      referenceWitnessPartAction_class D rho iota z h u
    change
      D.toQuotientGauge.vertexGauge (rho h x) (sigma h u).1 *
        (sigma h u).2 (rho h x) =
      M h (Quotient.mk D.part x) u.1 *
        (D.toQuotientGauge.vertexGauge x u.1 * u.2 x)
    rw [hClass, hSigmaVal]
    rw [← hRow h x u.1]
    group
  have hresult := htransport.trans htarget.symm
  simpa only [u, Equiv.apply_symm_apply] using hresult

end EffectiveGeometry

end SemigenericEPPA
