import SemigenericEPPA.Structure.FixedGoodSelectedRawLiftData
import SemigenericEPPA.Structure.SelectedRawEffectiveGroupAction
import SemigenericEPPA.Valuations.FactorialSelectedIndexedGaugeHAction
import SemigenericEPPA.Bridge.SelectedIndexedRawAutSubgroupLift

/-!
# One finite raw witness carrying ALL induced old automorphism groups

Assume a finite original raw R1--R3 rectangle presentation P and
one genuinely self-reversing effective colour. Globally fix ONE
factorial equal-fibre padded gauge Q, ONE actual-quotient gauge R,
ONE globally constant-good valuation skeleton K, and ONE finite
joint raw residual cover J BEFORE selecting any old subset S or
automorphism group H.

For every later genuine old H-action on an induced raw substructure
S, the SAME factorial replica action supplies its equivariant
occupied Option projection on the actual quotient, and preserves
the fixed quotient gauge F on the selected old labels. The SAME
canonical selected multiplier matrix and selected reference gauge
then produce a strict full two-layer effective H-action whose
ACTUALLY exchanged edges admit self-reversing raw representatives.
The fixed raw cover lifts that very H-action homomorphically to
the literal automorphism subgroup preserving E and every R_c.

In particular this proves the strong all-stabilizers input for
the existing exact coherent groupoid normal-form theorem.
It does NOT yet assert a coherent extension functor or typed
coherent EPPA; those follow only after the already formalized
individual raw connector extensions are assembled on this same
fixed witness.

Nothing depends on commutativity, s(1)=1, or global padded old F
invariance. No H-dependent change to K, R, J, or the old copy.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Globally choose one finite good raw cover and its literal old
embedding before ANY later S/H. Every genuine H-action by raw
automorphisms of every induced selected S lifts STRICTLY to the
actual raw automorphism group of that SAME cover, preserving
every embedded old zero-section vertex on the nose. -/
theorem exists_oneFixedRawCover_allSelectedAutGroupLifts
    (Praw : RawRectanglePresentation d A)
    (hGood : d.selfReverseEffective.Nonempty)
    (hsat : d.IsCongruenceSaturated) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (Q : IndexedGauge d.s
        (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A))
        (Quotient Praw.effectiveReduct.part))
      (R : IndexedGauge d.s
        (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A))
        (Quotient Q.toEffectiveGeometry.part))
      (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry),
      let D : EffectiveGeometry d.s A := Praw.effectiveReduct
      let B := Q.toEffectiveGeometry
      let old : A → Quotient D.part × Fin (coherentPaddingSize A) :=
        D.factorialAuxiliaryOldMap j
      let ψ : A → EffectiveWitnessVertex B :=
        fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
      ∃ J : FixedJointRawCover.{u, v, w, max u w, t}
          Praw K.toEffectiveGeometry ψ,
        Function.Injective ψ ∧
        (∀ x y : A,
          K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ Praw.part x y) ∧
        (∀ x y : A, ¬Praw.part x y →
          K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y) ∧
        Finite (EffectiveWitnessVertex B) ∧
        (∀ (H : Type t) [Group H] (S : Set A)
          (rhoS : H →* Equiv.Perm S),
          (∀ (h : H) (a b : S),
            Praw.part (rhoS h a).val (rhoS h b).val ↔
              Praw.part a.val b.val) →
          (∀ (h : H) (a b : S),
            Praw.colour (rhoS h a).val (rhoS h b).val =
              Praw.colour a.val b.val) →
          ∃ lift : H →* binaryRawAutSubgroup
              (fun X Y : RawCoverVertex
                  (EffectiveWitnessVertex B)
                  (UniversalResidualCarrier C) =>
                K.toEffectiveGeometry.part X.1 Y.1)
              (fun c X Y =>
                rawRel (rawCoverPresentation K.toEffectiveGeometry
                  J.code J.baseline J.baseline_reverse).toStructure c X Y),
            ∀ (h : H) (a : S),
              (lift h).val
                (ψ a.val, fun _ : EffectiveWitnessVertex B =>
                  (0 : UniversalResidualCarrier C)) =
                (ψ (rhoS h a).val,
                  fun _ : EffectiveWitnessVertex B =>
                    (0 : UniversalResidualCarrier C))) := by
  classical
  obtain ⟨j, Q, R, K, J, hj, _hQLabel,
      hBPart, hRLabel, hRConst, hRDiag, hRF, hKConst,
      _hBaseE, hBaseF, hψInj, hψE, hψF, hFinite⟩ :=
    Praw.exists_fixedGoodSelectedRawLiftData hGood
  let D : EffectiveGeometry d.s A := Praw.effectiveReduct
  let W : Type _ := Quotient D.part × Fin (coherentPaddingSize A)
  let B : EffectiveGeometry d.s W := Q.toEffectiveGeometry
  let old : A → W := D.factorialAuxiliaryOldMap j
  let ψ : A → EffectiveWitnessVertex B :=
    fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
  refine ⟨j, Q, R, K, J, hψInj, hψE, hψF, hFinite, ?_⟩
  intro H _ S rhoS hPart hColour
  obtain ⟨hEffE, hEffF⟩ :=
    Praw.selectedRawAction_preserves_effective S rhoS hPart hColour
  obtain ⟨iota, tau, proj, hIndex, hOld, hStable,
      hFixed, hSome, hProj, hProjClass, _hOldProj,
      hClass, hGaugeF⟩ :=
    R.exists_factorialSelectedGaugeAction_withProjection
      D j hj B hBPart hBaseF hRLabel hRF
      S rhoS hEffE hEffF
  let oldS : S → W := fun a => old a.val
  let cls : S → Quotient B.part :=
    fun a => Quotient.mk B.part (oldS a)
  let selected : Set W := Set.range oldS
  let occupied : Quotient B.part → Prop :=
    fun i => ∃ a : S, cls a = i
  let DS : EffectiveGeometry d.s S := D.induced S
  let raw : S → S → C :=
    fun a b => Praw.totalOldRawColour a.val b.val
  obtain ⟨hRawPhi, hRawReverse, hRawInvariant⟩ :=
    Praw.selectedRawInducedGroupData S rhoS hPart hColour
  have hEmbedClass (a : S) :
      Quotient.mk B.part (oldS a) = cls a := rfl
  have hEmbedAction (h : H) (a : S) :
      tau h (oldS a) = oldS (rhoS h a) :=
    hOld h a
  have hEmbedColour (a b : S) (hab : ¬DS.part a b) :
      B.F (oldS a) (oldS b) = DS.F a b :=
    hBaseF a.val b.val hab
  have hEmbedMem (a : S) : oldS a ∈ selected :=
    ⟨a, rfl⟩
  have hOldSection (a : S) :
      ψ a.val = B.gaugeOldWitnessVertex R.vertexGauge (oldS a) :=
    rfl
  exact R.exists_selectedIndexedRawAutSubgroupLift
    B hRLabel hRF hGood hRConst hRDiag K hKConst
    selected tau iota hStable hIndex hGaugeF
    S DS raw hRawPhi hRawReverse rhoS hRawInvariant
    occupied hFixed proj cls hClass hSome hProj hProjClass
    oldS hEmbedClass hEmbedAction hEmbedColour hEmbedMem
    hsat Praw ψ J hψInj hψE hOldSection hPart hColour

end RawRectanglePresentation

end SemigenericEPPA
