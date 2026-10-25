import SemigenericEPPA.Bridge.RelationalRawInducedColourTransport
import SemigenericEPPA.Structure.DLFFiniteUnrestrictedSemiCoherentEP

/-!
# Certified raw semi-coherence implies native relational semi-coherence

Start with an ARBITRARY selected cofinal family of finite raw
R1--R3 subgroup actions and re-interpret each selected pair as
a genuine original-relational pair. The old finite-group action
and all prescribed partial automorphism connectors are retained.
No local involution-safety condition enters this argument.

The result targets the NATIVE finite relational semi-coherent
extension property, with quantifiers over original structures,
E and every ordered R_c, not merely raw presentations.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- The unrestricted original-raw semi-coherent property gives
a genuinely original-relational selected finite subgroup action
family with strict H→K extensions and all original-language
partial isomorphism connectors. -/
theorem hasFiniteRelationalSemiCoherentEP_of_raw
    (d : RawDatum G C)
    (hSemi : d.HasFiniteRawSemiCoherentEP) :
    d.HasFiniteRelationalSemiCoherentEP := by
  classical
  obtain ⟨Selected, hCofinal, hExtension⟩ := hSemi
  refine ⟨(fun V _ R =>
    ∃ A : FiniteRawActionPair d V,
      Selected V A ∧ R = A.toRelationalActionPair), ?_, ?_⟩
  · intro X _ P hP
    obtain ⟨W, hW, B, e, hSelected, he, hp, hc⟩ :=
      hCofinal X hP.toRawPresentation
    letI : Finite W := hW
    refine ⟨W, hW, B.toRelationalActionPair, e,
      ⟨B, hSelected, rfl⟩, he, ?_, ?_⟩
    · intro x y
      exact hp x y
    · intro c x y
      change B.raw.colour (e x) (e y) = some c ↔
        rawRel P c x y
      rw [hc x y]
      exact hP.rawOption_some_iff c x y
  · intro V X _ _ A hSelected P hP e0 he0inj he0part he0raw
    obtain ⟨Araw, hAselected, hAeq⟩ := hSelected
    subst A
    let Praw : RawRectanglePresentation d X := hP.toRawPresentation
    have he0partRaw : ∀ x y : V,
        Praw.part (e0 x) (e0 y) ↔ Araw.raw.part x y :=
      he0part
    have he0colourRaw : ∀ x y : V,
        Praw.colour (e0 x) (e0 y) = Araw.raw.colour x y := by
      intro x y
      have hExact :=
        Araw.raw.toStructure_isRectangleStructure.rawOption_eq_of_induced
          hP e0 he0part he0raw x y
      exact hExact.trans (Araw.raw.toStructure_rawOption_eq x y)
    obtain ⟨W, hW, Braw, f, eP, hBselected,
      hePInj, hePPart, hePColour, hOld, hPartials⟩ :=
      hExtension V X Araw hAselected Praw e0
        he0inj he0partRaw he0colourRaw
    letI : Finite W := hW
    let fRel : FiniteRelationalActionPairEmbedding
        Araw.toRelationalActionPair
        Braw.toRelationalActionPair := {
      vertex := f.vertex
      vertex_injective := f.vertex_injective
      part_iff := by
        intro x y
        exact f.part_iff x y
      raw_iff := by
        intro c x y
        change Braw.raw.colour (f.vertex x) (f.vertex y) = some c ↔
          Araw.raw.colour x y = some c
        rw [f.colour_eq x y]
      groupMap := f.groupMap
      group_injective := f.group_injective
      group_action := f.group_action
    }
    refine ⟨W, hW, Braw.toRelationalActionPair, fRel, eP,
      ⟨Braw, hBselected, rfl⟩, hePInj, ?_, ?_, hOld, ?_⟩
    · intro x y
      exact hePPart x y
    · intro c x y
      change Braw.raw.colour (eP x) (eP y) = some c ↔
        rawRel P c x y
      rw [hePColour x y]
      exact hP.rawOption_some_iff c x y
    · intro T p hp hpPart hpRaw
      have hpColour : ∀ x y : T,
          Praw.colour (p x) (p y) =
            Praw.colour x.val y.val := by
        intro x y
        cases hc : hP.rawOption x.val y.val with
        | none =>
            have hbase : partRel P x.val y.val :=
              (hP.rawOption_none_iff x.val y.val).mp hc
            have htarget : partRel P (p x) (p y) :=
              (hpPart x y).mp hbase
            have hc' : hP.rawOption (p x) (p y) = none :=
              (hP.rawOption_none_iff (p x) (p y)).mpr htarget
            exact hc'.trans hc.symm
        | some c =>
            have hbase : rawRel P c x.val y.val :=
              (hP.rawOption_some_iff c x.val y.val).mp hc
            have htarget : rawRel P c (p x) (p y) :=
              (hpRaw c x y).mp hbase
            have hc' : hP.rawOption (p x) (p y) = some c :=
              (hP.rawOption_some_iff c (p x) (p y)).mpr htarget
            exact hc'.trans hc.symm
      exact hPartials T p hp hpPart hpColour

end RawDatum
end SemigenericEPPA
