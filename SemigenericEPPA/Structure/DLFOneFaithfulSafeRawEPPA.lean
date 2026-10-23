import SemigenericEPPA.Structure.DLFFaithfulRelativeGroupLift
import SemigenericEPPA.Structure.DLFSafeInvolutionPhaseAndRawBase
import SemigenericEPPA.Structure.DLFSafeLiftThroughEffectiveReduct
import SemigenericEPPA.Structure.DLFRawCoverEffectiveReduct
import SemigenericEPPA.Structure.DLFPhaseSafeRawJointWithBase
import SemigenericEPPA.Structure.DLFOneFixedRelativeSafeEffectiveWitness
import SemigenericEPPA.Structure.DLFPhaseSafeRawJointFromEffective
import SemigenericEPPA.Algebra.FiniteAffineResidualCode
import SemigenericEPPA.Structure.RawCover

/-!
# One finite original-language raw witness with faithful and globally safe H

Under one complete good affine congruence orbit, extend a faithful
strict raw H-action on a selected induced old S⊆P, without assuming
any H action on the rest of P. Use one fixed-seed factorial witness,
a relative regular phase and a single original R1--R3 raw cover.

Besides simultaneously extending all individual raw partial
isomorphisms, the same witness carries a faithful strict H-action
whose EVERY involution-reversed cross pair has an entire good
affine congruence orbit in the actual effective reduct.

No global saturation, no coherent connector choices, no DLF claimed.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {H : Type t} [Group H] [Finite H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Under one complete good orbit and an involution-safe action
on selected old S, there exists a single finite raw R1--R3 witness
which both lifts H STRICTLY and individually extends EVERY partial
raw isomorphism of the original full P.

All extensions use the same literal embedding into the original
raw relations. No coherent choice of individual connectors
is required or asserted. -/
theorem exists_faithfulGloballySafeRawEPPA_of_completeGoodOrbit
    (P : RawRectanglePresentation d A)
    (hGoodOrbit : d.HasCompleteGoodOrbit)
    (S : Set A) (rhoS : H →* Equiv.Perm S)
    (hFaithful : Function.Injective rhoS)
    (hPartOld : ∀ (h : H) (x y : S),
      P.part (rhoS h x).val (rhoS h y).val ↔
        P.part x.val y.val)
    (hColourOld : ∀ (h : H) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val)
    (hOldSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : S), ¬P.part x.val y.val →
        rhoS h x = y → rhoS h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x.val y.val)) :
    ∃ (W : Type (max u (max v (max w t))))
      (Pnew : RawRectanglePresentation d W)
      (e : A → W),
      Finite W ∧
      Function.Injective e ∧
      (∀ x y : A, Pnew.part (e x) (e y) ↔ P.part x y) ∧
      (∀ x y : A, Pnew.colour (e x) (e y) = P.colour x y) ∧
      (∃ lift : H →* Equiv.Perm W,
        Function.Injective lift ∧
        (∀ (h : H) (x : S),
          lift h (e x.val) = e (rhoS h x).val) ∧
        (∀ (h : H) (X Y : W),
          Pnew.part (lift h X) (lift h Y) ↔ Pnew.part X Y) ∧
        (∀ (h : H) (c : C) (X Y : W),
          rawRel Pnew.toStructure c (lift h X) (lift h Y) ↔
            rawRel Pnew.toStructure c X Y) ∧
        (∀ (h : H), h * h = 1 →
          ∀ (X Y : W), ¬Pnew.part X Y →
            lift h X = Y → lift h Y = X →
              d.GoodCompleteOrbitAt (Pnew.effectiveReduct.F X Y))) ∧
      (∀ (T : Set A) (p : T → A),
        Function.Injective p →
        (∀ x y : T, P.part x.val y.val ↔ P.part (p x) (p y)) →
        (∀ x y : T, P.colour (p x) (p y) = P.colour x.val y.val) →
        ∃ beta : Equiv.Perm W,
          (∀ x : T, beta (e x.val) = e (p x)) ∧
          (∀ X Y : W,
            Pnew.part (beta X) (beta Y) ↔ Pnew.part X Y) ∧
          (∀ c : C, ∀ X Y : W,
            rawRel Pnew.toStructure c (beta X) (beta Y) ↔
              rawRel Pnew.toStructure c X Y)) := by
  classical
  obtain ⟨g0, j, Q, R, K, J, hSeed, hPsiInj,
      hPsiPart, hPsiF, hFiniteEff, hAllGroups, hAllPartial⟩ :=
    P.exists_oneFixedRelativeSafeEffectiveWitness
      hGoodOrbit
  let B := Q.toEffectiveGeometry
  let V := EffectiveWitnessVertex B
  let psi : A → V :=
    fun x => B.gaugeOldWitnessVertex R.vertexGauge
      (P.effectiveReduct.factorialAuxiliaryOldMap j x)
  obtain ⟨Theta, hOld, hThetaE, hThetaF, hThetaSafe⟩ :=
    hAllGroups H S rhoS hPartOld hColourOld hOldSafe
  have hPhi : ∀ x y : A, ∀ c : C,
      P.colour x y = some c →
        d.phi c = K.toEffectiveGeometry.F (psi x) (psi y) := by
    intro x y c hc
    have hxy : ¬P.part x y := by
      intro hp
      have hn := (P.colour_none_iff x y).mpr hp
      rw [hc] at hn
      cases hn
    calc
      d.phi c = P.effectiveReduct.F x y :=
        P.effectiveReduct_crossColour x y c hc
      _ = K.toEffectiveGeometry.F (psi x) (psi y) :=
        (hPsiF x y hxy).symm
  letI : Finite V := hFiniteEff
  let L := UniversalResidualCarrier C
  letI : Finite L := finite_universalResidualCarrier
  obtain ⟨code⟩ := exists_universalAffineResidualCode d
  obtain ⟨hFiniteRaw, b, hb, lift, hOldColour, hZero,
      hBase, hPart, hRel, hPartials⟩ :=
    P.exists_relativePhaseRawJointWitness_of_effectiveAction_withBase
      K.toEffectiveGeometry code psi hPsiInj
      hPsiPart hPhi S rhoS hPartOld hColourOld
      Theta hOld hThetaE hThetaF
      (fun h x y hh hxy hx hy => hThetaSafe h hh x y hxy hx hy)
      hAllPartial
  let DPhase := (K.toEffectiveGeometry).phasePullback H
  let ePhase : A → V × H := fun x => (psi x, 1)
  let W := RawCoverVertex (V × H) L
  let Pnew : RawRectanglePresentation d W :=
    rawCoverPresentation DPhase code b hb
  let e : A → W :=
    fun x => (ePhase x, fun _ : V × H => (0 : L))
  let Aimg : Set V := embeddedOldSubset psi S
  have hA : ∀ (h : H) (x : V),
      x ∈ Aimg ↔ Theta h x ∈ Aimg :=
    embeddedOldSubset_invariant psi S rhoS Theta hOld
  let rhoPhase : H →* Equiv.Perm (V × H) :=
    relativePhaseAction Theta Aimg hA
  have hPhaseSafe : ∀ (h : H), h * h = 1 →
      ∀ (X Y : V × H), ¬DPhase.part X Y →
        rhoPhase h X = Y → rhoPhase h Y = X →
          d.GoodCompleteOrbitAt (DPhase.F X Y) := by
    intro h hh X Y hcross hxy hyx
    exact K.toEffectiveGeometry.relativePhaseAction_involutionCompleteOrbitSafe
      Theta Aimg hA hThetaSafe h hh X Y hcross hxy hyx
  have hProjection : ∀ (h : H) (X : W),
      rhoPhase h X.1 = (lift h X).1 := by
    intro h X
    exact (hBase h X).symm
  have hRawPart : ∀ X Y : W,
      Pnew.part X Y ↔ DPhase.part X.1 Y.1 := by
    intro X Y
    rfl
  have hRawF : ∀ X Y : W, ¬Pnew.part X Y →
      Pnew.effectiveReduct.F X Y = DPhase.F X.1 Y.1 := by
    intro X Y hcross
    exact rawCover_effectiveReduct_crossF DPhase code b hb X Y hcross
  have hSafeRaw : ∀ (h : H), h * h = 1 →
      ∀ (X Y : W), ¬Pnew.part X Y →
        lift h X = Y → lift h Y = X →
          d.GoodCompleteOrbitAt (Pnew.effectiveReduct.F X Y) := by
    intro h hh X Y hcross hxy hyx
    exact rawPresentation_involutionCompleteOrbitSafe_of_projection
      Pnew DPhase (fun X : W => X.1) rhoPhase lift
      (fun h X => (hProjection h X).symm)
      hRawPart hRawF hPhaseSafe h hh X Y hcross hxy hyx
  have hInjective : Function.Injective e := by
    intro x y he
    apply hPsiInj
    exact congrArg Prod.fst (congrArg Prod.fst he)
  have hPartOldEmbedding : ∀ x y : A,
      Pnew.part (e x) (e y) ↔ P.part x y := by
    intro x y
    change DPhase.part (ePhase x) (ePhase y) ↔ P.part x y
    exact hPsiPart x y
  have hColourOldEmbedding : ∀ x y : A,
      Pnew.colour (e x) (e y) = P.colour x y := by
    intro x y
    change rawCoverColour DPhase code b
      (ePhase x, fun _ : V × H => (0 : L))
      (ePhase y, fun _ : V × H => (0 : L)) = P.colour x y
    exact hOldColour x y
  have hOldLift : ∀ (h : H) (x : S),
      lift h (e x.val) = e (rhoS h x).val := by
    intro h x
    change lift h
        (ePhase x.val, fun _ : V × H => (0 : L)) =
      (ePhase (rhoS h x).val, fun _ : V × H => (0 : L))
    rw [hZero h (ePhase x.val)]
    change (relativePhaseAction Theta (embeddedOldSubset psi S)
      (embeddedOldSubset_invariant psi S rhoS Theta hOld)
      h (psi x.val, 1), fun _ : V × H => (0 : L)) =
      (ePhase (rhoS h x).val, fun _ : V × H => (0 : L))
    rw [relativePhaseAction_old Theta (embeddedOldSubset psi S)
      (embeddedOldSubset_invariant psi S rhoS Theta hOld)
      h (psi x.val) (show psi x.val ∈ embeddedOldSubset psi S
        from ⟨x, rfl⟩)]
    rw [hOld h x]
  have hFaithfulLift : Function.Injective lift :=
    faithfulRelativeGroupLift_of_oldAction
      S e hInjective rhoS hFaithful lift hOldLift
  refine ⟨W, Pnew, e, hFiniteRaw, hInjective,
    hPartOldEmbedding, hColourOldEmbedding,
    ⟨lift, hFaithfulLift, hOldLift, hPart, hRel, hSafeRaw⟩, ?_⟩
  intro T p hp hTp hTc
  exact hPartials T p hp hTp hTc

end RawRectanglePresentation

end SemigenericEPPA
