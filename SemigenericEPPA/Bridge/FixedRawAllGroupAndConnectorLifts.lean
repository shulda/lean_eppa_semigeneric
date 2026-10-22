import SemigenericEPPA.Bridge.FixedSelectedRawSubgroupLifts
import SemigenericEPPA.Structure.FixedGoodRawPartialConnector

/-!
# ONE prechosen finite raw witness for BOTH stabilizer groups and connectors

Assume a finite original raw rectangle presentation P, a genuinely
good effective colour and global congruence saturation of the good
effective set. Fix one factorial gauge Q, actual quotient gauge R,
one global constant-good two-layer skeleton K, one literal old
zero-section embedding, and one residual code/baseline/raw cover J
BEFORE any induced old subset, group action or partial isomorphism.

The certified same-data selected multiplier and occupied projection
construct strict homomorphic lifts of EVERY induced old raw
automorphism group on that witness. Independently, the certified
individual factorial partial E/F construction and fixed-cover raw
connector produce an automorphism of the EXACT SAME raw witness
for every original partial raw isomorphism.

No global H-action or individual connector is assumed. The two
extension APIs land in the same literal group of permutations
preserving E and every original R_c. The original raw zero section
is fixed across all choices.

This closes both prerequisites of the existing exact groupoid normal
form. The separate next theorem will instantiate its representative
objects, stabilizers and connectors, then translate the resulting
coherent functor to the upstream typed CoherentEPPAWitness predicate.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Quantifier order: ∃ one finite raw witness with both all-group
and all-individual-connector APIs; THEN ∀ selected S,H and p.
This is the precise common-witness input for coherent groupoids. -/
theorem exists_oneFixedRawCover_allGroupsAndPartialConnectors
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
                    (0 : UniversalResidualCarrier C))) ∧
        (∀ (S : Set A) (p : S → A),
          Function.Injective p →
          (∀ x y : S,
            Praw.part x.val y.val ↔ Praw.part (p x) (p y)) →
          (∀ x y : S,
            Praw.colour (p x) (p y) = Praw.colour x.val y.val) →
          ∃ beta : binaryRawAutSubgroup
              (fun X Y : RawCoverVertex
                  (EffectiveWitnessVertex B)
                  (UniversalResidualCarrier C) =>
                K.toEffectiveGeometry.part X.1 Y.1)
              (fun c X Y =>
                rawRel (rawCoverPresentation K.toEffectiveGeometry
                  J.code J.baseline J.baseline_reverse).toStructure c X Y),
            ∀ x : S,
              beta.val
                (ψ x.val, fun _ : EffectiveWitnessVertex B =>
                  (0 : UniversalResidualCarrier C)) =
                (ψ (p x), fun _ : EffectiveWitnessVertex B =>
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
  have hKOld (i k : Quotient B.part) (_ : i ≠ k) :
      K.colour (distinguishedWitnessPart B i)
        (distinguishedWitnessPart B k) = R.skeleton i k :=
    (hKConst _ _).trans (hRConst i k).symm
  refine ⟨j, Q, R, K, J, hψInj, hψE, hψF, hFinite, ?_, ?_⟩
  · intro H _ S rhoS hPart hColour
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
  
  · intro S p hp hPart hColour
    exact Praw.exists_rawPartialConnector_onFixedGoodCover
      j hj B hBPart hBaseF R hRLabel hRF hRDiag
      K hKOld J hψInj hψE S p hp hPart hColour

end RawRectanglePresentation

end SemigenericEPPA
