import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import SemigenericEPPA.Structure.RawPartialEffectiveReduct
import SemigenericEPPA.Valuations.EffectiveEPPA
import SemigenericEPPA.Algebra.FiniteAffineResidualCode
import SemigenericEPPA.Structure.RawCoverSectionLifts

/-!
# Unconditional finite ordinary EPPA for generalized semigeneric rectangles

The effective EPPA theorem already provides a single finite two-layer
effective valuation witness with a literal induced old embedding and
automorphism extensions for every partial effective E/F-isomorphism.

The R0 theorem provides a finite affine residual code
L=(C→ZMod4)×ZMod2 with correct typed reversal and sections.

The R1 theorem constructs the finite raw cover of that effective
witness, an induced old raw embedding using the canonical residual
sections, and raw-colour preserving automorphism lifts of EVERY
effective automorphism extending a partial raw map.

This file combines them. The witness and old embedding are fixed
BEFORE choosing the partial map; every injective partial old raw
isomorphism preserving E and all ordered raw colours extends on the
SAME finite literal raw rectangle presentation. It does not assert
coherent EPPA, general SAP, or any DLF group-action criterion.

Same-part raw colours are absent (none), while group-valued
effective same-part F-values are merely dummy, as in the manuscript.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {U : Type w}
variable {d : RawDatum G C}

/-- The concrete old effective valuation carrier, followed by one
unrestricted layer of additive raw residual valuations. Both
carriers are determined by the input raw presentation alone. -/
abbrev RawEPPAWitnessCarrier (P : RawRectanglePresentation d U) :=
  RawCoverVertex
    (EffectiveWitnessVertex P.effectiveReduct.uniformPaddedGeometry)
    (UniversalResidualCarrier C)

/-- Unconditional *ordinary* finite raw-colour EPPA in the exact
functional R1--R3 rectangle semantics.

A single fixed finite raw witness R contains P as an induced raw
substructure, and every injective partial map of P preserving and
reflecting E and preserving every ordered raw colour extends to
a genuine automorphism of R (including each raw predicate P_c).
No additional gauge, equal-part-size, residual-code, fixed-action,
or effective-colour-preservation assumption occurs in the statement.
-/
theorem RawRectanglePresentation.finite_rawEPPA_witness
    [Finite G] [Finite C] [Finite U]
    (P : RawRectanglePresentation d U) :
    Finite (RawEPPAWitnessCarrier P) ∧
    ∃ (R : RawRectanglePresentation d (RawEPPAWitnessCarrier P))
      (ψ : U → RawEPPAWitnessCarrier P),
      Function.Injective ψ ∧
      (∀ x y, R.part (ψ x) (ψ y) ↔ P.part x y) ∧
      (∀ x y, R.colour (ψ x) (ψ y) = P.colour x y) ∧
      (∀ (S : Set U) (p : S → U),
        Function.Injective p →
        (∀ x y : S, P.part x.val y.val ↔ P.part (p x) (p y)) →
        (∀ x y : S, P.colour (p x) (p y) = P.colour x.val y.val) →
        ∃ T : Equiv.Perm (RawEPPAWitnessCarrier P),
          (∀ x : S, T (ψ x.val) = ψ (p x)) ∧
          (∀ X Y, R.part (T X) (T Y) ↔ R.part X Y) ∧
          (∀ c : C, ∀ X Y,
            rawRel R.toStructure c (T X) (T Y) ↔
              rawRel R.toStructure c X Y)) := by
  classical
  let D₀ : EffectiveGeometry d.s U := P.effectiveReduct
  let W := EffectiveWitnessVertex D₀.uniformPaddedGeometry
  let L := UniversalResidualCarrier C
  letI : Finite L := finite_universalResidualCarrier
  let code : AffineResidualCode d L :=
    Classical.choice (exists_universalAffineResidualCode d)
  obtain ⟨hFiniteW, K, hK, he, hOldPart, hOldF, hEffectiveExt⟩ :=
    D₀.finite_effectiveEPPA_witness
  letI : Finite W := hFiniteW
  let D : EffectiveGeometry d.s W := K.toEffectiveGeometry
  let e : U → W := fun x =>
    D₀.uniformPaddedGeometry.oldWitnessVertex (D₀.paddedOldMap x)
  have he' : Function.Injective e := he
  have hPart (x y : U) :
      D.part (e x) (e y) ↔ P.part x y :=
    (hOldPart x y).trans (P.effectiveReduct_part x y)
  have hRawF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y) := by
    intro x y c hc
    have hNotPart : ¬P.part x y := by
      intro h
      have hn := (P.colour_none_iff x y).2 h
      rw [hc] at hn
      cases hn
    have hCross : ¬D₀.part x y := by
      intro h
      exact hNotPart ((P.effectiveReduct_part x y).mp h)
    calc
      d.phi c = D₀.F x y :=
        P.effectiveReduct_crossColour x y c hc
      _ = D.F (e x) (e y) := (hOldF x y hCross).symm
  obtain ⟨b, _, hb⟩ :=
    exists_finiteResidualBaseline D code.shift code.shift_reverse
  obtain ⟨hFiniteRaw, ψ, hψinj, hψPart, hψRaw, hLifts⟩ :=
    exists_sectionRawCoverEmbedding_withLifts
      P D code e he' hPart hRawF b hb
  let R : RawRectanglePresentation d (RawEPPAWitnessCarrier P) :=
    rawCoverPresentation D code b hb
  have hψColour (x y : U) :
      R.colour (ψ x) (ψ y) = P.colour x y := by
    cases hc : P.colour x y with
    | none =>
        have hP : P.part x y := (P.colour_none_iff x y).mp hc
        have hR : R.part (ψ x) (ψ y) := (hψPart x y).mpr hP
        exact ((R.colour_none_iff (ψ x) (ψ y)).mpr hR).trans hc.symm
    | some c =>
        have hPc : rawRel P.toStructure c x y :=
          (P.rawRel_toStructure c x y).mpr hc
        have hRc : rawRel R.toStructure c (ψ x) (ψ y) :=
          (hψRaw c x y).mpr hPc
        have hcR : R.colour (ψ x) (ψ y) = some c :=
          (R.rawRel_toStructure c (ψ x) (ψ y)).mp hRc
        exact hcR.trans hc.symm
  refine ⟨hFiniteRaw, R, ψ, hψinj, hψPart, hψColour, ?_⟩
  intro S p hp hPartOld hColourOld
  have hPartEff : ∀ x y : S,
      D₀.part x.val y.val ↔ D₀.part (p x) (p y) := by
    intro x y
    exact (P.effectiveReduct_part x.val y.val).trans
      ((hPartOld x y).trans
        (P.effectiveReduct_part (p x) (p y)).symm)
  have hFEff : ∀ x y : S, ¬D₀.part x.val y.val →
      D₀.F (p x) (p y) = D₀.F x.val y.val := by
    intro x y hxy
    have hSource : ¬P.part x.val y.val := by
      intro h
      exact hxy ((P.effectiveReduct_part x.val y.val).mpr h)
    have hTarget : ¬P.part (p x) (p y) := by
      intro h
      exact hSource ((hPartOld x y).mpr h)
    exact P.effectiveReduct_equalColour
      (p x) (p y) x.val y.val (hColourOld x y) hTarget
  obtain ⟨θ, hθOld, hθPart, hθF⟩ :=
    hEffectiveExt S p hp hPartEff hFEff
  exact hLifts S p θ hColourOld hθOld hθPart hθF

end SemigenericEPPA
