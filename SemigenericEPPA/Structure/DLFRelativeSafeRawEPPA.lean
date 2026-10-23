import SemigenericEPPA.Structure.DLFOneFixedRelativeSafeEffectiveWitness
import SemigenericEPPA.Structure.DLFPhaseSafeRawJointFromEffective
import SemigenericEPPA.Algebra.FiniteAffineResidualCode
import SemigenericEPPA.Structure.RawCover

/-!
# Relative safe EPPA on ONE finite original-language raw witness

Assume only that the good raw-effective fibres contain ONE complete
affine congruence orbit. Let a finite group H act by genuine raw
automorphisms on a distinguished induced S of an arbitrary old raw
R1--R3 rectangle P. Assume the exact DLF safety condition:
each H-involution exchanging an actual old cross-E pair has its
ENTIRE congruence orbit good.

The certified explicit-seed factorial theorem chooses a finite
two-layer effective witness independently of H, extends the
prescribed H action homomorphically, and extends every individual
old partial raw map on the same old zero section. The certified
relative-phase construction then acts regularly on extra vertices,
is trivially phased on S, and lifts both action modes through ONE
actual finite raw cover using an automatically selected invariant
reference respecting ALL prescribed old raw colours.

The resulting witness preserves the entire original E+R_c
binary language. H acts homomorphically; every partial raw map
of the FULL old P separately has a raw automorphism extension
on this VERY SAME witness. No false assertion that H acts on
the rest of P, no saturated-all-good-fibres hypothesis,
and no order-two requirement on old-sector reversals.

The construction is relative to the prescribed H action.
The later finite group cover must make the new action faithful
and globally safe for semicoherent EP; no DLF group is claimed.
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
theorem exists_relativeSafeRawEPPA_of_completeGoodOrbit
    (P : RawRectanglePresentation d A)
    (hGoodOrbit : d.HasCompleteGoodOrbit)
    (S : Set A) (rhoS : H →* Equiv.Perm S)
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
        (∀ (h : H) (x : S),
          lift h (e x.val) = e (rhoS h x).val) ∧
        (∀ (h : H) (X Y : W),
          Pnew.part (lift h X) (lift h Y) ↔ Pnew.part X Y) ∧
        (∀ (h : H) (c : C) (X Y : W),
          rawRel Pnew.toStructure c (lift h X) (lift h Y) ↔
            rawRel Pnew.toStructure c X Y)) ∧
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
    P.exists_oneFixedRelativeSafeEffectiveWitness (t := t)
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
      hPart, hRel, hPartials⟩ :=
    P.exists_relativePhaseRawJointWitness_of_effectiveAction
      K.toEffectiveGeometry code psi hPsiInj
      hPsiPart hPhi S rhoS hPartOld hColourOld
      Theta hOld hThetaE hThetaF hThetaSafe hAllPartial
  let DPhase := (K.toEffectiveGeometry).phasePullback H
  let ePhase : A → V × H := fun x => (psi x, 1)
  let W := RawCoverVertex (V × H) L
  let Pnew : RawRectanglePresentation d W :=
    rawCoverPresentation DPhase code b hb
  let e : A → W :=
    fun x => (ePhase x, fun _ : V × H => (0 : L))
  refine ⟨W, Pnew, e, hFiniteRaw, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y h
    apply hPsiInj
    exact congrArg Prod.fst (congrArg Prod.fst h)
  · intro x y
    change DPhase.part (ePhase x) (ePhase y) ↔ P.part x y
    exact hPsiPart x y
  · intro x y
    change rawCoverColour DPhase code b
      (ePhase x, fun _ : V × H => (0 : L))
      (ePhase y, fun _ : V × H => (0 : L)) = P.colour x y
    exact hOldColour x y
  · refine ⟨lift, ?_, hPart, hRel⟩
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
    rfl
  · intro T p hp hTp hTc
    exact hPartials T p hp hTp hTc

end RawRectanglePresentation

end SemigenericEPPA
