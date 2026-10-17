import SemigenericEPPA.Structure.FiniteOnePointRaw
import SemigenericEPPA.Structure.RelationalRoundtrip
import SemigenericEPPA.Structure.EffectiveGeometry

/-!
# Genuine finite one-point SAP for the literal R1--R3 language

The previous raw SAP theorem used a compact functional interface:
two one-point effective geometries with compatible raw colour functions.

Here the INPUTS are actual IsRectangleStructure objects in the literal
AllThoseEPPA binary language L_C, with exact common induced structure
on the old vertex set V. We derive the common effective geometry, the
two one-point effective extensions and the exact raw-colour agreement,
then invoke the fully verified finite raw one-point amalgamation theorem.

The OUTPUT is one genuine literal R1--R3 structure on V ⊕ Bool with
both E and every P_c reflected and preserved on each one-point side.
The two new vertices are distinct by the existing injections.

No extra order, S-saturation, commutativity, or HKN EPPA is assumed.
This is the finite ONE-POINT SAP theorem; arbitrary finite SAP by
iteration of one-point diagrams is a separate formalization gate.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- An honest pair of one-point R1--R3 extensions with EXACT same
induced raw-colour structure on the common old carrier. -/
structure LiteralOnePointDiagram (d : RawDatum G C) (V : Type w) where
  base : Structure (rectangleLanguage C) V
  left : Structure (rectangleLanguage C) (Option V)
  right : Structure (rectangleLanguage C) (Option V)
  baseValid : IsRectangleStructure d base
  leftValid : IsRectangleStructure d left
  rightValid : IsRectangleStructure d right
  left_part : ∀ a b : V,
    partRel left (some a) (some b) ↔ partRel base a b
  right_part : ∀ a b : V,
    partRel right (some a) (some b) ↔ partRel base a b
  left_raw : ∀ c : C, ∀ a b : V,
    rawRel left c (some a) (some b) ↔ rawRel base c a b
  right_raw : ∀ c : C, ∀ a b : V,
    rawRel right c (some a) (some b) ↔ rawRel base c a b

namespace LiteralOnePointDiagram

variable (Q : LiteralOnePointDiagram d V)

/-- The actual common effective rectangle geometry from the base. -/
noncomputable def baseEffective : EffectiveGeometry d.s V :=
  Q.baseValid.toEffectiveGeometry

/-- The effective colours of a true one-point side agree literally
with those of the old base on ALL ordered old pairs, including
dummy same-E values, because all underlying raw predicates agree. -/
private theorem old_effective_eq
    (S : Structure (rectangleLanguage C) (Option V))
    (hS : IsRectangleStructure d S)
    (hpart : ∀ a b : V,
      partRel S (some a) (some b) ↔ partRel Q.base a b)
    (hraw : ∀ c : C, ∀ a b : V,
      rawRel S c (some a) (some b) ↔ rawRel Q.base c a b)
    (a b : V) :
    hS.effectiveTotal (some a) (some b) =
      Q.baseValid.effectiveTotal a b := by
  by_cases hab : partRel Q.base a b
  · have hsab : partRel S (some a) (some b) :=
      (hpart a b).2 hab
    rw [hS.effectiveTotal_same (some a) (some b) hsab,
      Q.baseValid.effectiveTotal_same a b hab]
  · have hsab : ¬partRel S (some a) (some b) := by
      intro h
      exact hab ((hpart a b).1 h)
    have hrawOld := Q.baseValid.chosenRaw_spec a b hab
    have hrawSide :
        rawRel S (Q.baseValid.chosenRaw a b hab) (some a) (some b) :=
      (hraw (Q.baseValid.chosenRaw a b hab) a b).2 hrawOld
    have hchoice :
        hS.chosenRaw (some a) (some b) hsab =
          Q.baseValid.chosenRaw a b hab :=
      hS.chosenRaw_unique (some a) (some b) hsab
        (Q.baseValid.chosenRaw a b hab) hrawSide
    rw [hS.effectiveTotal_cross (some a) (some b) hsab,
      Q.baseValid.effectiveTotal_cross a b hab]
    change
      d.phi (hS.chosenRaw (some a) (some b) hsab) =
        d.phi (Q.baseValid.chosenRaw a b hab)
    exact congrArg d.phi hchoice

/-- The left structure becomes a genuine one-point extension of
the EXACT common effective geometry. -/
noncomputable def leftEffective : OnePointEffectiveExtension Q.baseEffective where
  geometry := Q.leftValid.toEffectiveGeometry
  old_part := Q.left_part
  old_F := Q.old_effective_eq Q.left Q.leftValid Q.left_part Q.left_raw

/-- The analogous right one-point effective extension. -/
noncomputable def rightEffective : OnePointEffectiveExtension Q.baseEffective where
  geometry := Q.rightValid.toEffectiveGeometry
  old_part := Q.right_part
  old_F := Q.old_effective_eq Q.right Q.rightValid Q.right_part Q.right_raw

/-- Canonical complete raw colours on the left one-point side. -/
noncomputable def leftRaw :
    OnePointRawColouring Q.baseEffective Q.leftEffective where
  colour := Q.leftValid.rawOption
  none_iff := Q.leftValid.rawOption_none_iff
  reverse := Q.leftValid.rawOption_reverse
  projects := Q.leftValid.rawOption_phi_effectiveTotal

/-- Canonical complete raw colours on the right one-point side. -/
noncomputable def rightRaw :
    OnePointRawColouring Q.baseEffective Q.rightEffective where
  colour := Q.rightValid.rawOption
  none_iff := Q.rightValid.rawOption_none_iff
  reverse := Q.rightValid.rawOption_reverse
  projects := Q.rightValid.rawOption_phi_effectiveTotal

/-- Both canonical raw options agree on the common old carrier,
as a CONSEQUENCE of the literal induced P_c agreement. -/
theorem raw_agree : AgreeOnOldRaw Q.leftRaw Q.rightRaw := by
  intro a b
  by_cases hab : partRel Q.base a b
  · have hl : partRel Q.left (some a) (some b) :=
      (Q.left_part a b).2 hab
    have hr : partRel Q.right (some a) (some b) :=
      (Q.right_part a b).2 hab
    have hnl := (Q.leftValid.rawOption_none_iff (some a) (some b)).2 hl
    have hnr := (Q.rightValid.rawOption_none_iff (some a) (some b)).2 hr
    exact hnl.trans hnr.symm
  · let c : C := Q.baseValid.chosenRaw a b hab
    have hc : rawRel Q.base c a b :=
      Q.baseValid.chosenRaw_spec a b hab
    have hl : Q.leftValid.rawOption (some a) (some b) = some c :=
      (Q.leftValid.rawOption_some_iff c (some a) (some b)).2
        ((Q.left_raw c a b).2 hc)
    have hr : Q.rightValid.rawOption (some a) (some b) = some c :=
      (Q.rightValid.rawOption_some_iff c (some a) (some b)).2
        ((Q.right_raw c a b).2 hc)
    exact hl.trans hr.symm

/-- Literal FINITE one-point strong amalgamation. The output is an
actual R1--R3 relational structure, with E and every P_c exactly
reflected and preserved on BOTH embeddings of Option V. -/
theorem finite_onePoint_strong_amalgamation
    [Fintype V] :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier V),
      IsRectangleStructure d S ∧
      (∀ x y : Option V,
        partRel S (firstOnePoint x) (firstOnePoint y) ↔
          partRel Q.left x y) ∧
      (∀ x y : Option V,
        partRel S (secondOnePoint x) (secondOnePoint y) ↔
          partRel Q.right x y) ∧
      (∀ c : C, ∀ x y : Option V,
        rawRel S c (firstOnePoint x) (firstOnePoint y) ↔
          rawRel Q.left c x y) ∧
      (∀ c : C, ∀ x y : Option V,
        rawRel S c (secondOnePoint x) (secondOnePoint y) ↔
          rawRel Q.right c x y) := by
  obtain ⟨S, hS, hLpart, hRpart, hLraw, hRraw⟩ :=
    finite_raw_onePoint_strong_amalgamation Q.leftRaw Q.rightRaw Q.raw_agree
  refine ⟨S, hS, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact hLpart x y
  · intro x y
    exact hRpart x y
  · intro c x y
    exact (hLraw c x y).trans (Q.leftValid.rawOption_some_iff c x y)
  · intro c x y
    exact (hRraw c x y).trans (Q.rightValid.rawOption_some_iff c x y)

end LiteralOnePointDiagram
end SemigenericEPPA
