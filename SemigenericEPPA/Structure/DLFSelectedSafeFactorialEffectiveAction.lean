import SemigenericEPPA.Bridge.DLFExplicitSeedInvolutionSafeHAction
import SemigenericEPPA.Structure.SelectedRawEffectiveGroupAction
import SemigenericEPPA.Valuations.FactorialSelectedIndexedGaugeHAction
import SemigenericEPPA.Structure.FixedGoodSelectedRawLiftData

/-!
# Relative DLF: a genuine selected raw group acts safely on the SAME fixed witness

Fix any original finite R1--R3 presentation Praw and a factorial
effective padded base B with its globally fixed old injection j,
one true-quotient indexed gauge R, and one constant skeleton K,
ALL with the same explicit chosen complete-good-orbit seed g0.

For ANY genuine H-action by raw automorphisms on an induced
old subset S⊆Praw, the certified factorial construction returns
one actual padded old-label H-action tau, class-index action iota,
and equivariant occupied-only projection to S. The same tau
preserves the fixed indexed-gauge effective F on the selected
old image. The new explicit-seed selected multiplier theorem
then produces one honest full two-layer H-action Theta preserving
all witness E/F, extending the literal old zero-section on S,
and with every involution-swapped cross-witness pair in a
complete GOOD affine congruence orbit.

The only safety hypothesis concerns involutions swapping genuine
old cross-E pairs in S. No global IsCongruenceSaturated, no
H-invariance on the original points outside S, no H-dependent
new padded base, gauge, skeleton, or other witness choice.

This is the relative effective group-action bridge. Phase
regularisation and old NON-H-invariant B raw-colour preservation
are separate subsequent steps.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w} [Fintype A]
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The SAME fixed factorial effective witness admits a full
strict H-action extending every selected raw H-action whose
actual old involutions have complete good-colour orbits.

No separate auxiliary action, multiplier family, equivariant
projection or witness action is assumed; all are constructed
from the genuine old selected raw automorphism action. -/
theorem exists_selectedSafeEffectiveAction_onFixedSeedGauge
    (Praw : RawRectanglePresentation d A)
    (g0 : G) (hGoodOrbit : d.GoodCompleteOrbitAt g0)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (B : EffectiveGeometry d.s
      (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A)))
    (hBPart : ∀ x y : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      B.part x y ↔ x.1 = y.1)
    (hBOldF : ∀ x y : A, ¬Praw.effectiveReduct.part x y →
      B.F (Praw.effectiveReduct.factorialAuxiliaryOldMap j x)
        (Praw.effectiveReduct.factorialAuxiliaryOldMap j y) =
          Praw.effectiveReduct.F x y)
    (R : IndexedGauge d.s
      (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A))
      (Quotient B.part))
    (hRLabel : ∀ x : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      R.label x = Quotient.mk B.part x)
    (hRF : ∀ x y : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      ¬B.part x y → R.effective x y = B.F x y)
    (hRConst : ∀ i k : Quotient B.part, R.skeleton i k = g0)
    (hRDiag : ∀ x : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      R.vertexGauge x (R.label x) = 1)
    (K : EffectiveWitnessSkeleton B)
    (hKConst : ∀ q r : EffectiveWitnessPart B,
      K.colour q r = g0)
    (S : Set A) (rhoS : H →* Equiv.Perm S)
    (hPart : ∀ (h : H) (a b : S),
      Praw.part (rhoS h a).val (rhoS h b).val ↔
        Praw.part a.val b.val)
    (hColour : ∀ (h : H) (a b : S),
      Praw.colour (rhoS h a).val (rhoS h b).val =
        Praw.colour a.val b.val)
    (hOldInvolSafe : ∀ (h : H), h * h = 1 →
      ∀ (a b : S), ¬Praw.part a.val b.val →
        rhoS h a = b → rhoS h b = a →
          d.GoodCompleteOrbitAt
            (Praw.effectiveReduct.F a.val b.val)) :
    let old : A →
      (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A)) :=
      Praw.effectiveReduct.factorialAuxiliaryOldMap j
    let psi : A → EffectiveWitnessVertex B :=
      fun a => B.gaugeOldWitnessVertex R.vertexGauge (old a)
    ∃ Theta : H →* Equiv.Perm (EffectiveWitnessVertex B),
      (∀ (h : H) (a : S),
        Theta h (psi a.val) = psi (rhoS h a).val) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex B),
        K.toEffectiveGeometry.part (Theta h X) (Theta h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex B),
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (Theta h X) (Theta h Y) =
            K.toEffectiveGeometry.F X Y) ∧
      (∀ (h : H), h * h = 1 →
        ∀ (X Y : EffectiveWitnessVertex B),
          ¬K.toEffectiveGeometry.part X Y →
          Theta h X = Y → Theta h Y = X →
          d.GoodCompleteOrbitAt (K.toEffectiveGeometry.F X Y)) := by
  let D : EffectiveGeometry d.s A := Praw.effectiveReduct
  let old : A →
      Quotient D.part × Fin (coherentPaddingSize A) :=
    D.factorialAuxiliaryOldMap j
  let psi : A → EffectiveWitnessVertex B :=
    fun a => B.gaugeOldWitnessVertex R.vertexGauge (old a)
  obtain ⟨hEffE, hEffF⟩ :=
    Praw.selectedRawAction_preserves_effective S rhoS hPart hColour
  obtain ⟨iota, tau, proj, hIndex, hOld, hStable,
      hFixed, hSome, hProj, hProjClass, _hOldProj,
      hClass, hGaugeF⟩ :=
    R.exists_factorialSelectedGaugeAction_withProjection
      D j hj B hBPart hBOldF hRLabel hRF
      S rhoS hEffE hEffF
  let oldS : S →
      Quotient D.part × Fin (coherentPaddingSize A) :=
    fun a => old a.val
  let cls : S → Quotient B.part :=
    fun a => Quotient.mk B.part (oldS a)
  let selected : Set
      (Quotient D.part × Fin (coherentPaddingSize A)) :=
    Set.range oldS
  let occupied : Quotient B.part → Prop :=
    fun i => ∃ a : S, cls a = i
  let DS : EffectiveGeometry d.s S := D.induced S
  have hOldSafe : ∀ (h : H), h * h = 1 →
      ∀ (a b : S), ¬DS.part a b →
        rhoS h a = b → rhoS h b = a →
          d.GoodCompleteOrbitAt (DS.F a b) := by
    intro h htwo a b hab hswapA hswapB
    exact hOldInvolSafe h htwo a b hab hswapA hswapB
  have hEmbedClass (a : S) :
      Quotient.mk B.part (oldS a) = cls a := rfl
  have hEmbedAction (h : H) (a : S) :
      tau h (oldS a) = oldS (rhoS h a) := hOld h a
  have hEmbedColour (a b : S) (hab : ¬DS.part a b) :
      B.F (oldS a) (oldS b) = DS.F a b :=
    hBOldF a.val b.val hab
  have hEmbedMem (a : S) : oldS a ∈ selected :=
    ⟨a, rfl⟩
  have hG0Fixed : d.s g0 = g0 :=
    d.selfReverseEffective_subset_fixed
      (d.good_of_completeOrbitAt g0 hGoodOrbit)
  obtain ⟨Theta, hThetaOld, hThetaE, hThetaF, hThetaSafe⟩ :=
    R.exists_selectedInvolutionOrbitSafeEffectiveHAction_of_seed
      B hRLabel hRF g0 hG0Fixed hGoodOrbit
      hRConst hRDiag K hKConst
      selected tau iota hStable hIndex hGaugeF
      DS rhoS hOldSafe occupied hFixed proj cls
      hClass hSome hProj hProjClass
      oldS hEmbedClass hEmbedAction hEmbedColour hEmbedMem
  refine ⟨Theta, ?_, hThetaE, hThetaF, hThetaSafe⟩
  intro h a
  change Theta h
      (B.gaugeOldWitnessVertex R.vertexGauge (oldS a)) =
    B.gaugeOldWitnessVertex R.vertexGauge (oldS (rhoS h a))
  calc
    Theta h (B.gaugeOldWitnessVertex R.vertexGauge (oldS a)) =
        B.gaugeOldWitnessVertex R.vertexGauge (tau h (oldS a)) :=
      hThetaOld h (oldS a) (hEmbedMem a)
    _ = B.gaugeOldWitnessVertex R.vertexGauge (oldS (rhoS h a)) :=
      congrArg (B.gaugeOldWitnessVertex R.vertexGauge)
        (hEmbedAction h a)

end RawRectanglePresentation

end SemigenericEPPA
