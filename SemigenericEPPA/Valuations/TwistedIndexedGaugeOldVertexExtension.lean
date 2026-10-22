import SemigenericEPPA.Valuations.IndexedGaugePartialWitnessCompatibility
import SemigenericEPPA.Valuations.TwistedOldVertexExtension

/-!
# Individual partial E/F-automorphism of ONE fixed indexed-gauge witness

Generalize the certified (3.14)--(3.19) individual partial-map
construction to an arbitrary preselected IndexedGauge R on the
ACTUAL old quotient of D. The old zero-section is literally
  x ↦ D.gaugeOldWitnessVertex R.vertexGauge x,
and the fixed witness skeleton K agrees with R.skeleton on all
distinct neutral part pairs.

All twists, permutations, prescribed multipliers and global
completion are constructed exactly as in the already certified
ordinary effective EPPA proof, but without changing to the
canonical quotient-gauge old embedding or to a different skeleton.

The prerequisites on m are the actual fixed-gauge (3.14)/(3.15)
equations. An earlier theorem constructs them directly from a
selected partial E/F-isomorphism. This is a conditional effective
connector extension theorem on the same good fixed witness; the
final raw lift and coherent groupoid remain separate gates.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

theorem exists_twistedIndexedGaugeWitnessAutomorphism_extending_old
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (R : IndexedGauge s V (Quotient D.part))
    [LinearOrder (EffectiveWitnessPart D)]
    (hK : ∀ i j : Quotient D.part, i ≠ j →
      K.colour (distinguishedWitnessPart D i)
        (distinguishedWitnessPart D j) = R.skeleton i j)
    (S : Set V) (p : S → V)
    (ι : Equiv.Perm (Quotient D.part))
    (π : Equiv.Perm V)
    (hπ : ∀ z : V,
      Quotient.mk D.part (π z) =
        ι (Quotient.mk D.part z))
    (hp : ∀ x : S, π x.val = p x)
    (m : Quotient D.part → Quotient D.part → G)
    (hinc : ∀ (x : S) (j : Quotient D.part),
      (∃ y : S, Quotient.mk D.part y.val = j) →
      m (Quotient.mk D.part x.val) j *
          R.vertexGauge x.val j =
        R.vertexGauge (p x) (ι j))
    (hcompat : ∀ i j : Quotient D.part,
      (∃ x : S, Quotient.mk D.part x.val = i) →
      (∃ y : S, Quotient.mk D.part y.val = j) →
      i ≠ j →
        s.normalized (m i j) *
            (R.skeleton (ι i) (ι j))⁻¹ *
              m j i =
          (R.skeleton i j)⁻¹) :
    ∃ T : EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D,
      (∀ x : S,
        T (D.gaugeOldWitnessVertex R.vertexGauge x.val) = D.gaugeOldWitnessVertex R.vertexGauge (p x)) ∧
      (∀ X Y : EffectiveWitnessVertex D,
        K.toEffectiveGeometry.part (T X) (T Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ X Y : EffectiveWitnessVertex D,
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (T X) (T Y) =
            K.toEffectiveGeometry.F X Y) := by
  classical
  let cls : V → Quotient D.part := Quotient.mk D.part
  let a : V → Quotient D.part → G := R.vertexGauge
  let visited : Quotient D.part → Prop :=
    fun j => ∃ y : S, cls y.val = j
  have hvisited (x : S) (j : Quotient D.part) (hj : visited j) :
      m (cls x.val) j * a x.val j = a (p x) (ι j) :=
    hinc x j hj
  let L : Quotient D.part → V → G :=
    oldPartialGaugeTwist S p ι visited cls a m
  have hL (j : Quotient D.part) (hj : visited j) (z : V) :
      L j z = 1 :=
    oldPartialGaugeTwist_visited S p ι visited cls a m j hj z
  let σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D :=
    twistedWitnessPartPerm D ι π L
  let ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q) :=
    twistedWitnessFibreEquiv D ι π L hπ
  let P : EffectiveWitnessPart D → Prop :=
    IsVisitedNeutralPart D visited
  let mw : EffectiveWitnessPart D → EffectiveWitnessPart D → G :=
    neutralPrescribedMultiplier D m
  let T : EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D :=
    prescribedEffectiveWitnessAutomorphism D K σ ρ P mw
  have hmWitness :
      ∀ q r : EffectiveWitnessPart D,
        P q → P r → q ≠ r →
          s.normalized (mw q r) *
              (K.colour (σ q) (σ r))⁻¹ * mw r q =
            (K.colour q r)⁻¹ := by
    intro q r hq hr hqr
    exact neutralPrescribedMultiplier_compatible_onIndexedGauge
      D K R hK ι π L visited hL m
      (fun i j hi hj hij => hcompat i j hi hj hij)
      q r hq hr hqr
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x
    have hPx : P (oldWitnessPart D x.val) := by
      change visited (cls x.val) ∧
        (neutralPartValuation : V → G) = neutralPartValuation
      exact ⟨⟨x, rfl⟩, rfl⟩
    have hιx :
        ι (cls x.val) = cls (p x) := by
      calc
        ι (cls x.val) = cls (π x.val) := (hπ x.val).symm
        _ = cls (p x) := congrArg cls (hp x)
    have hσx :
        σ (oldWitnessPart D x.val) =
          oldWitnessPart D (p x) := by
      calc
        σ (oldWitnessPart D x.val) =
          distinguishedWitnessPart D (ι (cls x.val)) :=
            twistedWitnessPartPerm_distinguished
              D ι π L (cls x.val)
              (hL (cls x.val) ⟨x, rfl⟩)
        _ = oldWitnessPart D (p x) :=
          congrArg (distinguishedWitnessPart D) hιx
    have hρx :
        (ρ (oldWitnessPart D x.val) ⟨x.val, rfl⟩).val =
          p x := by
      change π x.val = p x
      exact hp x
    have hcross :
        ∀ (r : EffectiveWitnessPart D)
          (hr : r ≠ oldWitnessPart D x.val),
          mw (oldWitnessPart D x.val) r *
              (D.gaugeOldWitnessVertex R.vertexGauge x.val).crossIncidence r hr =
            (D.gaugeOldWitnessVertex R.vertexGauge (p x)).crossIncidence
              (σ r) (by
                intro heq
                apply hr
                apply σ.injective
                exact heq.trans hσx.symm) := by
      intro r hr
      have hc := oldPartialGaugeTwist_targetIncidence
        S p ι visited cls a m hvisited π r.2 x r.1
      have hcoord :
          a (p x) (ι r.1) * (σ r).2 (π x.val) =
            m (cls x.val) r.1 *
              (a x.val r.1 * r.2 x.val) := by
        change a (p x) (ι r.1) *
              (twistPartValuation π (L r.1) r.2) (π x.val) =
            m (cls x.val) r.1 *
              (a x.val r.1 * r.2 x.val)
        exact hc
      rw [hp x] at hcoord
      change m (cls x.val) r.1 *
          (a x.val r.1 * r.2 x.val) =
        a (p x) (ι r.1) * (σ r).2 (p x)
      exact hcoord.symm
    exact prescribedEffectiveWitnessAutomorphism_maps_gaugeOld
      D K R.vertexGauge σ ρ P mw x.val (p x) hPx hσx hρx hcross
  · intro X Y
    exact prescribedEffectiveWitnessAutomorphism_part_iff
      D K σ ρ P mw X Y
  · intro X Y hXY
    exact prescribedEffectiveWitnessAutomorphism_colour
      D K σ ρ P mw hmWitness X Y hXY


end SemigenericEPPA
