import SemigenericEPPA.Structure.Language

/-!
# Canonical raw/effective colours of an admissible relational structure

The manuscript uses a function F(x,y) only for ordered pairs from
distinct E-classes.  This file derives that function from the L_C relations,
rather than making it an independent axiom or choosing colours on same-part
pairs.  The unique raw colour exists by axiom R2.

The reversal theorem and exact rectangle equation below make the relational
definition interoperable with the already-verified rank-one/gauge algebra.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {C : Type u} {V : Type v} {G : Type w} [Group G]
variable {d : RawDatum G C} {A : Structure (rectangleLanguage C) V}

namespace IsRectangleStructure

/-- Symmetry of the cross-part condition from R1. -/
theorem cross_symm (h : IsRectangleStructure d A)
    {x y : V} (hxy : ¬partRel A x y) :
    ¬partRel A y x := by
  intro hyx
  exact hxy (h.parts_equiv.symm hyx)

/-- A canonical raw colour on an ordered cross-part pair.
The apparent dependence on the proof of being cross-part is irrelevant
by Lean's proof irrelevance. -/
noncomputable def chosenRaw (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y) : C :=
  Classical.choose (h.cross_unique x y hxy)

/-- The selected raw colour really is present on the ordered pair. -/
theorem chosenRaw_spec (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y) :
    rawRel A (h.chosenRaw x y hxy) x y :=
  (Classical.choose_spec (h.cross_unique x y hxy)).1

/-- Any present raw colour equals the selected one. -/
theorem chosenRaw_unique (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y)
    (c : C) (hc : rawRel A c x y) :
    h.chosenRaw x y hxy = c :=
  ((Classical.choose_spec (h.cross_unique x y hxy)).2 c hc).symm

/-- The R2 reversal axiom holds as an equation of the extracted colours. -/
theorem chosenRaw_reverse (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y)
    (hyx : ¬partRel A y x) :
    h.chosenRaw y x hyx = d.reverse (h.chosenRaw x y hxy) := by
  have hr : rawRel A (d.reverse (h.chosenRaw x y hxy)) y x :=
    h.reverse_of_raw (h.chosenRaw_spec x y hxy)
  exact h.chosenRaw_unique y x hyx _ hr

/-- Effective colour F(x,y) = φ(c) on cross-part ordered pairs. -/
noncomputable def chosenEffective (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y) : G :=
  d.phi (h.chosenRaw x y hxy)

/-- Raw reversal descends to the affine effective anti-involution. -/
theorem chosenEffective_reverse (h : IsRectangleStructure d A)
    (x y : V) (hxy : ¬partRel A x y)
    (hyx : ¬partRel A y x) :
    h.chosenEffective y x hyx =
      d.s (h.chosenEffective x y hxy) := by
  change d.phi (h.chosenRaw y x hyx) =
    d.s (d.phi (h.chosenRaw x y hxy))
  rw [h.chosenRaw_reverse x y hxy hyx]
  exact d.equivariant _

/-- Given the first cross-part pair in a rectangle, the other three
are automatically cross-part as well. -/
theorem cross_square (h : IsRectangleStructure d A)
    (x₀ x₁ y₀ y₁ : V)
    (hx : partRel A x₀ x₁)
    (hy : partRel A y₀ y₁)
    (h00 : ¬partRel A x₀ y₀) :
    (¬partRel A x₀ y₁) ∧
      (¬partRel A x₁ y₀) ∧
      (¬partRel A x₁ y₁) := by
  constructor
  · intro h01
    exact h00 (h.parts_equiv.trans h01 (h.parts_equiv.symm hy))
  constructor
  · intro h10
    exact h00 (h.parts_equiv.trans hx h10)
  · intro h11
    exact h00 (h.parts_equiv.trans hx
      (h.parts_equiv.trans h11 (h.parts_equiv.symm hy)))

/-- Exactly the effective-colour rectangle law, now for the
unique effective colours extracted from the relational R1--R3 class.
The four cross-part proofs are supplied explicitly to avoid
inventing values on within-part pairs. -/
theorem chosenEffective_rectangle (h : IsRectangleStructure d A)
    (x₀ x₁ y₀ y₁ : V)
    (hx : partRel A x₀ x₁)
    (hy : partRel A y₀ y₁)
    (h00 : ¬partRel A x₀ y₀)
    (h01 : ¬partRel A x₀ y₁)
    (h10 : ¬partRel A x₁ y₀)
    (h11 : ¬partRel A x₁ y₁) :
    (h.chosenEffective x₀ y₀ h00)⁻¹ *
      h.chosenEffective x₀ y₁ h01 =
    (h.chosenEffective x₁ y₀ h10)⁻¹ *
      h.chosenEffective x₁ y₁ h11 := by
  change
    (d.phi (h.chosenRaw x₀ y₀ h00))⁻¹ *
      d.phi (h.chosenRaw x₀ y₁ h01) =
    (d.phi (h.chosenRaw x₁ y₀ h10))⁻¹ *
      d.phi (h.chosenRaw x₁ y₁ h11)
  exact h.rectangle x₀ x₁ y₀ y₁ hx hy
    (h.chosenRaw x₀ y₀ h00) (h.chosenRaw x₀ y₁ h01)
    (h.chosenRaw x₁ y₀ h10) (h.chosenRaw x₁ y₁ h11)
    (h.chosenRaw_spec x₀ y₀ h00)
    (h.chosenRaw_spec x₀ y₁ h01)
    (h.chosenRaw_spec x₁ y₀ h10)
    (h.chosenRaw_spec x₁ y₁ h11)

end IsRectangleStructure
end SemigenericEPPA
