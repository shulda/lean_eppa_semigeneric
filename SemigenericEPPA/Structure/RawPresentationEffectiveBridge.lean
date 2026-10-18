import SemigenericEPPA.Structure.EffectiveGeometry
import SemigenericEPPA.Structure.RawPresentation

/-!
# Exact effective reduct of a functional raw rectangle presentation

A literal raw R1–R3 presentation P has a certified relational
structure P.toStructure. The canonical effective geometry extracted
from this structure satisfies E exactly as P.part and has group
colour phi(c) on each old cross-part edge with raw colour c.

The statements below establish this *literal* compatibility, rather
than only a gauge equivalence. They provide the input needed to run
finite effective EPPA on a raw presentation and embed its raw
colours into the subsequent residual cover.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- The canonical effective reduct of a raw presentation is the
effective geometry extracted from its exact relational structure. -/
noncomputable def RawRectanglePresentation.effectiveReduct
    (P : RawRectanglePresentation d V) :
    EffectiveGeometry d.s V :=
  P.toStructure_isRectangleStructure.toEffectiveGeometry

/-- The old E relation is preserved and reflected literally
by the effective-reduct construction. -/
@[simp] theorem RawRectanglePresentation.effectiveReduct_part
    (P : RawRectanglePresentation d V)
    (x y : V) :
    P.effectiveReduct.part x y ↔ P.part x y := Iff.rfl

/-- Every old raw cross-colour c has exactly effective colour phi(c)
in the canonical effective reduct, with no arbitrary choices left
in the conclusion. -/
theorem RawRectanglePresentation.effectiveReduct_crossColour
    (P : RawRectanglePresentation d V)
    (x y : V) (c : C)
    (hc : P.colour x y = some c) :
    d.phi c = P.effectiveReduct.F x y := by
  let h : IsRectangleStructure d P.toStructure :=
    P.toStructure_isRectangleStructure
  have hraw : rawRel P.toStructure c x y := hc
  have hcross : ¬partRel P.toStructure x y := by
    intro hpart
    have hn := (P.colour_none_iff x y).2 hpart
    rw [hc] at hn
    cases hn
  have hchosen : h.chosenRaw x y hcross = c :=
    h.chosenRaw_unique x y hcross c hraw
  change d.phi c = h.effectiveTotal x y
  rw [h.effectiveTotal_cross x y hcross]
  change d.phi c = d.phi (h.chosenRaw x y hcross)
  exact (congrArg d.phi hchosen).symm

/-- No effective equality needs to be assumed separately for
two old edges carrying the same raw colour. -/
theorem RawRectanglePresentation.effectiveReduct_equalColour
    (P : RawRectanglePresentation d V)
    (x y u v : V)
    (hcol : P.colour x y = P.colour u v)
    (hcross : ¬P.part x y) :
    P.effectiveReduct.F x y = P.effectiveReduct.F u v := by
  have hc : ∃ c : C, P.colour x y = some c := by
    cases h : P.colour x y with
    | none =>
      exact False.elim (hcross ((P.colour_none_iff x y).1 h))
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c,hc⟩ := hc
  have hc' : P.colour u v = some c := hcol.symm.trans hc
  exact (P.effectiveReduct_crossColour x y c hc).symm.trans
    (P.effectiveReduct_crossColour u v c hc')

end SemigenericEPPA
