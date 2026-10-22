import SemigenericEPPA.Valuations.FixedFactorialEffectivePartialConnector
import SemigenericEPPA.Structure.FixedRawCoverIndividualAutConnector
import SemigenericEPPA.Structure.SelectedRawEffectiveGroupAction

/-!
# Every old raw partial map extends inside one preselected good raw cover

Fix ONE factorial auxiliary effective geometry B, ONE actual-quotient
indexed gauge R, ONE valuation skeleton K, ONE gauge-valued old
zero-section and ONE universal affine raw cover J with its immutable
baseline and code. All are selected before choosing a partial map.

For any genuine partial isomorphism of the original raw R1--R3
presentation, its E/F reduct preserves the actual noncommutative
rectangle colours. The fixed factorial connector theorem provides
a full effective automorphism of K, extending this exact same old
zero-section. The conditional fixed-cover raw connector theorem
then produces an automorphism in the literal subgroup preserving
E and EVERY original raw R_c. No change to J, K, R or old embedding.

This is the individual connector gate for the SAME fixed raw witness
used by the strict stabilizer-group lifts. The final quantifier-order
theorem will choose all fixed data once and combine both APIs.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Conditional only on the already fixed good finite witness data,
EVERY original raw partial isomorphism has a connector inside the
ACTUAL raw automorphism subgroup of that same fixed joint cover.

There is no separate effective-connector existence hypothesis. -/
theorem exists_rawPartialConnector_onFixedGoodCover
    (Praw : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (B : EffectiveGeometry d.s
      (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A)))
    (hBPart : ∀ z w : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A), B.part z w ↔ z.1 = w.1)
    (hBOldF : ∀ x y : A, ¬Praw.effectiveReduct.part x y →
      B.F (Praw.effectiveReduct.factorialAuxiliaryOldMap j x)
        (Praw.effectiveReduct.factorialAuxiliaryOldMap j y) =
          Praw.effectiveReduct.F x y)
    (R : IndexedGauge d.s
      (Quotient Praw.effectiveReduct.part × Fin (coherentPaddingSize A))
      (Quotient B.part))
    (hRLabel : ∀ z : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      R.label z = Quotient.mk B.part z)
    (hRF : ∀ z w : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      ¬B.part z w → R.effective z w = B.F z w)
    (hRDiag : ∀ z : Quotient Praw.effectiveReduct.part ×
        Fin (coherentPaddingSize A),
      R.vertexGauge z (R.label z) = 1)
    (K : EffectiveWitnessSkeleton B)
    (hK : ∀ i k : Quotient B.part, i ≠ k →
      K.colour (distinguishedWitnessPart B i)
        (distinguishedWitnessPart B k) = R.skeleton i k)
    (J : FixedJointRawCover.{u, v, w, max u w, t}
      Praw K.toEffectiveGeometry
      (fun x : A =>
        B.gaugeOldWitnessVertex R.vertexGauge
          (Praw.effectiveReduct.factorialAuxiliaryOldMap j x)))
    (hPsiInj : Function.Injective
      (fun x : A =>
        B.gaugeOldWitnessVertex R.vertexGauge
          (Praw.effectiveReduct.factorialAuxiliaryOldMap j x)))
    (hPsiPart : ∀ x y : A,
      K.toEffectiveGeometry.part
        (B.gaugeOldWitnessVertex R.vertexGauge
          (Praw.effectiveReduct.factorialAuxiliaryOldMap j x))
        (B.gaugeOldWitnessVertex R.vertexGauge
          (Praw.effectiveReduct.factorialAuxiliaryOldMap j y)) ↔
        Praw.part x y)
    (S : Set A) (p : S → A)
    (hp : Function.Injective p)
    (hPart : ∀ x y : S,
      Praw.part x.val y.val ↔ Praw.part (p x) (p y))
    (hColour : ∀ x y : S,
      Praw.colour (p x) (p y) = Praw.colour x.val y.val) :
    ∃ beta : binaryRawAutSubgroup
        (fun X Y : RawCoverVertex
            (EffectiveWitnessVertex B) (UniversalResidualCarrier C) =>
          K.toEffectiveGeometry.part X.1 Y.1)
        (fun c X Y =>
          rawRel (rawCoverPresentation K.toEffectiveGeometry
            J.code J.baseline J.baseline_reverse).toStructure c X Y),
      ∀ x : S,
        beta.val
          (B.gaugeOldWitnessVertex R.vertexGauge
            (Praw.effectiveReduct.factorialAuxiliaryOldMap j x.val),
            fun _ : EffectiveWitnessVertex B =>
              (0 : UniversalResidualCarrier C)) =
          (B.gaugeOldWitnessVertex R.vertexGauge
            (Praw.effectiveReduct.factorialAuxiliaryOldMap j (p x)),
            fun _ : EffectiveWitnessVertex B =>
              (0 : UniversalResidualCarrier C)) := by
  let D : EffectiveGeometry d.s A := Praw.effectiveReduct
  have hEffE : ∀ x y : S, D.part x.val y.val ↔
      D.part (p x) (p y) := by
    intro x y
    exact (Praw.effectiveReduct_part x.val y.val).trans
      ((hPart x y).trans
        (Praw.effectiveReduct_part (p x) (p y)).symm)
  have hEffF : ∀ x y : S, ¬D.part x.val y.val →
      D.F (p x) (p y) = D.F x.val y.val := by
    intro x y hxy
    have hOrig : ¬Praw.part x.val y.val := by
      intro hp
      exact hxy ((Praw.effectiveReduct_part x.val y.val).mpr hp)
    have hNew : ¬Praw.part (p x) (p y) := by
      intro hp
      exact hOrig ((hPart x y).mpr hp)
    exact Praw.effectiveReduct_equalColour
      (p x) (p y) x.val y.val (hColour x y) hNew
  obtain ⟨theta, hThetaOld, hThetaE, hThetaF⟩ :=
    D.exists_fixedFactorialEffectivePartialConnector
      j hj B hBPart hBOldF R hRLabel hRF hRDiag
      K hK S p hp hEffE hEffF
  exact J.exists_rawAutConnector_of_effectiveConnector
    Praw K.toEffectiveGeometry
    (fun x : A =>
      B.gaugeOldWitnessVertex R.vertexGauge
        (D.factorialAuxiliaryOldMap j x))
    hPsiInj hPsiPart S p hPart hColour
    theta hThetaOld hThetaE hThetaF

end RawRectanglePresentation

end SemigenericEPPA
