import SemigenericEPPA.Structure.RawPresentation
import SemigenericEPPA.Structure.EffectiveColour

/-!
# Exact functional presentation of an existing rectangle structure

Every relational object of K(G,s,φ) canonically determines an
Option-valued raw-colour function, undefined precisely on same-part
pairs. This produces a functional RawRectanglePresentation.

Conversely the relational interpretation of this presentation has
exactly the SAME E relation and the SAME raw-colour predicates
as the starting structure, not merely an equisatisfiable theory.

This is the reverse direction of RawPresentation.toStructure. It
provides an auditable interface to transport old one-point structures
into explicit effective/raw amalgamation data.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C} {A : Structure (rectangleLanguage C) V}

namespace IsRectangleStructure

/-- The canonical optional raw colour, genuinely undefined exactly
on within-part pairs. -/
noncomputable def rawOption (h : IsRectangleStructure d A)
    (x y : V) : Option C :=
  if hxy : partRel A x y then none
  else some (h.chosenRaw x y hxy)

/-- Exact equality between functional raw-colour data and
the original relational P_c predicate. -/
theorem rawOption_some_iff (h : IsRectangleStructure d A)
    (c : C) (x y : V) :
    h.rawOption x y = some c ↔ rawRel A c x y := by
  by_cases hxy : partRel A x y
  · have hno : ¬rawRel A c x y := by
      intro hc
      exact h.raw_only_cross c x y hc hxy
    simp [rawOption, hxy, hno]
  · change
      (if hh : partRel A x y then (none : Option C)
        else some (h.chosenRaw x y hh)) = some c ↔
      rawRel A c x y
    simp only [dif_neg hxy, Option.some.injEq]
    constructor
    · intro hch
      rw [← hch]
      exact h.chosenRaw_spec x y hxy
    · intro hc
      exact h.chosenRaw_unique x y hxy c hc

/-- Functional colour is absent iff the two vertices lie in
the same E-class, including the diagonal. -/
theorem rawOption_none_iff (h : IsRectangleStructure d A)
    (x y : V) :
    h.rawOption x y = none ↔ partRel A x y := by
  by_cases hxy : partRel A x y
  · simp [rawOption, hxy]
  · simp [rawOption, hxy]

/-- The raw-colour option function retains the exact involution
of the original relational language. -/
theorem rawOption_reverse (h : IsRectangleStructure d A)
    (x y : V) :
    h.rawOption y x = Option.map d.reverse (h.rawOption x y) := by
  by_cases hxy : partRel A x y
  · have hyx := h.parts_equiv.symm hxy
    simp [rawOption, hxy, hyx]
  · have hyx := h.cross_symm hxy
    change
      (if hy : partRel A y x then (none : Option C)
        else some (h.chosenRaw y x hy)) =
      Option.map d.reverse
        (if hx : partRel A x y then (none : Option C)
          else some (h.chosenRaw x y hx))
    rw [dif_neg hyx, dif_neg hxy]
    simp only [Option.map_some, Option.some.injEq]
    exact h.chosenRaw_reverse x y hxy hyx

/-- Repackage the original structure in the functional presentation.
This is not a new mathematical assumption or completion. -/
noncomputable def toRawPresentation (h : IsRectangleStructure d A) :
    RawRectanglePresentation d V where
  part := partRel A
  part_equiv := h.parts_equiv
  colour := h.rawOption
  colour_none_iff := h.rawOption_none_iff
  colour_reverse := h.rawOption_reverse
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy
      c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11
    exact h.rectangle x₀ x₁ y₀ y₁ hx hy
      c₀₀ c₀₁ c₁₀ c₁₁
      ((h.rawOption_some_iff c₀₀ x₀ y₀).mp h00)
      ((h.rawOption_some_iff c₀₁ x₀ y₁).mp h01)
      ((h.rawOption_some_iff c₁₀ x₁ y₀).mp h10)
      ((h.rawOption_some_iff c₁₁ x₁ y₁).mp h11)

/-- The functional/relational round trip preserves E literally. -/
theorem rawPresentation_part_exact (h : IsRectangleStructure d A)
    (x y : V) :
    partRel h.toRawPresentation.toStructure x y ↔ partRel A x y := by
  rfl

/-- The functional/relational round trip preserves every raw
binary colour predicate literally. No redescription of the
original structure is required. -/
theorem rawPresentation_colour_exact (h : IsRectangleStructure d A)
    (c : C) (x y : V) :
    rawRel h.toRawPresentation.toStructure c x y ↔
      rawRel A c x y := by
  change h.rawOption x y = some c ↔ rawRel A c x y
  exact h.rawOption_some_iff c x y

end IsRectangleStructure
end SemigenericEPPA
