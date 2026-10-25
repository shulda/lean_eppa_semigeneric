import SemigenericEPPA.Bridge.NativeRelationalSemiCoherentPositive
import SemigenericEPPA.Bridge.SemiCoherentRelationalDLFClassification

/-!
# Native original-relational semi-coherent EP implies raw semi-coherence

Convert a selected cofinal family of *genuine original E/R_c*
finite subgroup actions into the corresponding complete raw
Option-C presentations. The selected finite automorphism
groups are the actual original-relational full-Aut subgroups
transported along the already certified equality of Aut groups.

All old-group action homomorphisms and all partial-automorphism
connectors are retained, with no safety assumption. Combined
with the independently proved converse this identifies the
paper's native property with our machine-certified raw one.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- An arbitrary selected native original-relational
semi-coherent family yields the unrestricted finite raw
semi-coherent subgroup extension property. -/
theorem hasFiniteRawSemiCoherentEP_of_relational
    (d : RawDatum G C)
    (hSemi : d.HasFiniteRelationalSemiCoherentEP) :
    d.HasFiniteRawSemiCoherentEP := by
  classical
  obtain ⟨Selected, hCofinal, hExtension⟩ := hSemi
  refine ⟨(fun V _ A =>
    ∃ B : FiniteRelationalActionPair d V,
      Selected V B ∧ A = B.toRawActionPair), ?_, ?_⟩
  · intro X _ P
    obtain ⟨W, hW, B, e, hSelected, he, hp, hraw⟩ :=
      hCofinal X P.toStructure P.toStructure_isRectangleStructure
    letI : Finite W := hW
    refine ⟨W, hW, B.toRawActionPair, e,
      ⟨B, hSelected, rfl⟩, he, hp, ?_⟩
    intro x y
    have hcolour :=
      P.toStructure_isRectangleStructure.rawOption_eq_of_induced
        B.isRectangle e hp hraw x y
    exact hcolour.trans (P.toStructure_rawOption_eq x y)
  · intro V X _ _ A hSelected P e0 he0inj he0part he0colour
    obtain ⟨Arel, hAselected, hAeq⟩ := hSelected
    subst A
    have he0partRel : ∀ x y : V,
        partRel P.toStructure (e0 x) (e0 y) ↔
          partRel Arel.rel x y :=
      he0part
    have he0rawRel : ∀ (c : C) (x y : V),
        rawRel P.toStructure c (e0 x) (e0 y) ↔
          rawRel Arel.rel c x y := by
      intro c x y
      calc
        rawRel P.toStructure c (e0 x) (e0 y) ↔
            P.colour (e0 x) (e0 y) = some c :=
          P.rawRel_toStructure c (e0 x) (e0 y)
        _ ↔ Arel.toRawActionPair.raw.colour x y = some c := by
          rw [he0colour x y]
        _ ↔ rawRel Arel.rel c x y :=
          Arel.isRectangle.rawOption_some_iff c x y
    obtain ⟨W, hW, Brel, f, eP, hBselected, hePInj,
      hePPart, hePRaw, hOld, hPartials⟩ :=
      hExtension V X Arel hAselected P.toStructure
        P.toStructure_isRectangleStructure
        e0 he0inj he0partRel he0rawRel
    letI : Finite W := hW
    let fRaw : FiniteRawActionPairEmbedding
        Arel.toRawActionPair Brel.toRawActionPair := {
      vertex := f.vertex
      vertex_injective := f.vertex_injective
      part_iff := by
        intro x y
        exact f.part_iff x y
      colour_eq := by
        intro x y
        exact Arel.isRectangle.rawOption_eq_of_induced
          Brel.isRectangle f.vertex f.part_iff f.raw_iff x y
      groupMap := f.groupMap
      group_injective := f.group_injective
      group_action := f.group_action
    }
    refine ⟨W, hW, Brel.toRawActionPair, fRaw, eP,
      ⟨Brel, hBselected, rfl⟩, hePInj, hePPart, ?_, hOld, ?_⟩
    · intro x y
      have hcolour :=
        P.toStructure_isRectangleStructure.rawOption_eq_of_induced
          Brel.isRectangle eP hePPart hePRaw x y
      exact hcolour.trans (P.toStructure_rawOption_eq x y)
    · intro T p hp hpPart hpColour
      have hpRaw : ∀ (c : C) (x y : T),
          rawRel P.toStructure c x.val y.val ↔
            rawRel P.toStructure c (p x) (p y) := by
        intro c x y
        change P.colour x.val y.val = some c ↔
          P.colour (p x) (p y) = some c
        rw [hpColour x y]
      exact hPartials T p hp hpPart hpRaw

/-- The EXACT native original-relational semi-coherent EP
property is logically equivalent to the unrestricted raw
semi-coherent EP class predicate. Neither side imposes
local involution safety on the cofinal finite action family. -/
theorem finiteRelationalSemiCoherentEP_iff_raw
    (d : RawDatum G C) :
    d.HasFiniteRelationalSemiCoherentEP ↔
      d.HasFiniteRawSemiCoherentEP := by
  constructor
  · exact d.hasFiniteRawSemiCoherentEP_of_relational
  · exact d.hasFiniteRelationalSemiCoherentEP_of_raw

/-- Fully native original-relational semi-coherent EP is
equivalent to DLF for the genuine countable homogeneous
original E/R_c relational structure. -/
theorem finiteRelationalSemiCoherentEP_iff_relationalDLF
    (d : RawDatum G C) :
    d.HasFiniteRelationalSemiCoherentEP ↔
      d.HasCountableRelationalHomogeneousDLF :=
  (d.finiteRelationalSemiCoherentEP_iff_raw).trans
    (d.finiteRawSemiCoherentEP_iff_relationalDLF)

end RawDatum
end SemigenericEPPA
