import SemigenericEPPA.Bridge.FixedRawAllGroupAndConnectorLifts
import SemigenericEPPA.Bridge.GlobalRawFunctorFromGroupAndConnectors
import SemigenericEPPA.Bridge.ExactRawAutomorphismGroups
import SemigenericEPPA.Bridge.RawExactFunctorToTypedCoherent

/-!
# Finite typed coherent EPPA for saturated generalized semigeneric rectangles

The positive nontrivial-G good-colour theorem fixes ONE finite
factorial two-layer effective witness, ONE literal old zero section,
and ONE finite raw residual cover before all old partial maps.
Its all-stabilizers and all-individual-connectors conclusions
land in the same actual group of permutations preserving the
complete original E and every raw R_c predicate.

The previously certified generic exact groupoid normal form
then chooses stabilizer representations and whole-witness connectors
once per old raw-isomorphism component. This gives ONE coherent
functor from the exact partial-isomorphism groupoid into the actual
raw automorphism group of this same cover; identity, composition
and literal old-vertex extension follow automatically.

Finally the already verified exact-to-upstream converter delivers
an actual IsCoherentEPPAWitness in the ORIGINAL binary language,
not just in the E/F effective reduct or a recoded gauge language.

This theorem assumes a nonempty genuine self-reversing effective
set and complete congruence-orbit saturation; together with the
independently certified necessary criterion and the G=1 theorem,
it is the desired positive branch of the coherent classification.
No Ramsey, DLF, or additional finite SAP conclusion is asserted.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- For every finite original raw R1--R3 structure with at least one
good self-reversing effective value and a globally saturated good
set, ONE FINITE raw presentation Q has a coherent typed EPPA
embedding in the original language with strict coherent groupoid
extensions. This includes arbitrary nonabelian G, arbitrary affine
anti-involution and nonzero s(1). -/
theorem finite_typedCoherentEPPA_witness_of_saturated
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
      let psi : A → EffectiveWitnessVertex B :=
        fun a => B.gaugeOldWitnessVertex R.vertexGauge (old a)
      ∃ J : FixedJointRawCover.{u, v, w, max u w, w}
          Praw K.toEffectiveGeometry psi,
        Finite (RawCoverVertex
          (EffectiveWitnessVertex B) (UniversalResidualCarrier C)) ∧
        ∃ e : Structure.Embedding
          (rectangleTrivialAction C) Praw.toStructure
          (rawCoverPresentation K.toEffectiveGeometry
            J.code J.baseline J.baseline_reverse).toStructure,
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) e := by
  classical
  obtain ⟨j, Q, R, K, J, hPsiInj, hPsiPart, _hPsiF,
      hFiniteEff, hAllGroups, hAllConnectors⟩ :=
    Praw.exists_oneFixedRawCover_allGroupsAndPartialConnectors.{u, v, w, w}
      hGood hsat
  let D : EffectiveGeometry d.s A := Praw.effectiveReduct
  let B := Q.toEffectiveGeometry
  let old : A → Quotient D.part × Fin (coherentPaddingSize A) :=
    D.factorialAuxiliaryOldMap j
  let psi : A → EffectiveWitnessVertex B :=
    fun a => B.gaugeOldWitnessVertex R.vertexGauge (old a)
  let W := RawCoverVertex
    (EffectiveWitnessVertex B) (UniversalResidualCarrier C)
  let Qraw : RawRectanglePresentation d W :=
    rawCoverPresentation K.toEffectiveGeometry
      J.code J.baseline J.baseline_reverse
  let psiRaw : A → W :=
    fun a => (psi a, fun _ : EffectiveWitnessVertex B =>
      (0 : UniversalResidualCarrier C))
  let Aut : Subgroup (Equiv.Perm W) :=
    Qraw.actualRawAutomorphismGroup
  have hInjective : Function.Injective psiRaw := by
    intro a b hab
    apply hPsiInj
    exact congrArg Prod.fst hab
  have hPart : ∀ a b : A,
      Qraw.part (psiRaw a) (psiRaw b) ↔
        Praw.part a b :=
    hPsiPart
  have hColour : ∀ a b : A,
      Qraw.colour (psiRaw a) (psiRaw b) =
        Praw.colour a b :=
    J.old_colour
  have hGroups :
      ∀ (S : Set A),
        ∃ rho : ExactPartialIso Praw S S →* Aut,
          ∀ (h : ExactPartialIso Praw S S) (a : S),
            (rho h).val (psiRaw a.val) =
              psiRaw (h.toEquiv a).val := by
    intro S
    let H := ExactPartialIso Praw S S
    let rhoS : H →* Equiv.Perm S :=
      ExactPartialIso.autAction Praw S
    have hE : ∀ (h : H) (a b : S),
        Praw.part (rhoS h a).val (rhoS h b).val ↔
          Praw.part a.val b.val := by
      intro h a b
      exact (ExactPartialIso.autAction_part Praw S h a b).symm
    have hRaw : ∀ (h : H) (a b : S),
        Praw.colour (rhoS h a).val (rhoS h b).val =
          Praw.colour a.val b.val :=
      ExactPartialIso.autAction_colour Praw S
    obtain ⟨lift, hOld⟩ :=
      hAllGroups H S rhoS hE hRaw
    refine ⟨lift, ?_⟩
    intro h a
    exact hOld h a
  have hConnectors :
      ∀ (S T : Set A) (f : ExactPartialIso Praw S T),
        ∃ beta : Aut,
          ∀ a : S,
            beta.val (psiRaw a.val) =
              psiRaw (f.toEquiv a).val := by
    intro S T f
    let p : S → A := fun a => (f.toEquiv a).val
    have hp : Function.Injective p :=
      Subtype.val_injective.comp f.toEquiv.injective
    have hE : ∀ a b : S,
        Praw.part a.val b.val ↔
          Praw.part (p a) (p b) := by
      intro a b
      exact (f.part_iff a b).symm
    have hRaw : ∀ a b : S,
        Praw.colour (p a) (p b) =
          Praw.colour a.val b.val := by
      intro a b
      exact f.colour_eq a b
    obtain ⟨beta, hOld⟩ :=
      hAllConnectors S p hp hE hRaw
    refine ⟨beta, ?_⟩
    intro a
    exact hOld a
  obtain ⟨F, _hId, hComp, hOld⟩ :=
    Praw.exists_globalCoherentExactRawFunctor_of_groupsAndConnectors
      Aut psiRaw hGroups hConnectors
  have hFiniteRaw : Finite W := by
    letI : Finite (EffectiveWitnessVertex B) := hFiniteEff
    letI : Finite (UniversalResidualCarrier C) :=
      finite_universalResidualCarrier
    exact finite_rawCoverVertices
  obtain ⟨embedding, hCoherent⟩ :=
    Praw.coherentTypedEPPA_of_exactRawFunctor
      Qraw psiRaw hInjective hPart hColour F hComp hOld
  exact ⟨j, Q, R, K, J, hFiniteRaw, embedding, hCoherent⟩

end RawRectanglePresentation

end SemigenericEPPA
