import SemigenericEPPA.Structure.RawPresentation
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# The genuine 3+1 raw obstruction: a tripleton E-part and a singleton

The no-good-colour necessity proof for nontrivial effective G
uses four original old vertices: a,b,c in one E-part and v
in a distinct singleton E-part. Specify the THREE directed raw
colours of v to a,b,c completely independently.

Use nested options:
  v = none
  a = some none
  b = some (some false)
  c = some (some true).

The E-relation is equality of outer Option.isSome. Every ordered
cross edge has a unique raw colour, with reversal on the opposite
orientation. There are no nontrivial rectangles because one of
the two distinct E-parts is a singleton, so the construction is
valid for ANY group, affine anti-involution, and raw-colour choices.

The following module will choose raw representatives over effective
colours delta,1,1 and construct the actual typed partial involution
a↔b fixing c on their induced tripleton E-part.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- True four-vertex raw rectangle structure with old cross-edge
colours prescribed independently by c : Option Bool → C. -/
noncomputable def RawDatum.threePlusOneRawPresentation
    (d : RawDatum G C) (c : Option Bool → C) :
    RawRectanglePresentation d (Option (Option Bool)) where
  part := fun x y => x.isSome = y.isSome
  part_equiv := by
    constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  colour := fun x y =>
    match x, y with
    | none, some i => some (c i)
    | some i, none => some (d.reverse (c i))
    | _, _ => none
  colour_none_iff := by
    intro x y
    cases x <;> cases y <;> simp
  colour_reverse := by
    intro x y
    cases x <;> cases y <;>
      simp [d.reverse_involutive]
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    have hrepeat : x₀ = x₁ ∨ y₀ = y₁ := by
      cases x₀ <;> cases x₁ <;>
        cases y₀ <;> cases y₁ <;> simp_all
    rcases hrepeat with h | h
    · subst x₁
      have h0 : c₀₀ = c₁₀ :=
        Option.some.inj (h00.symm.trans h10)
      have h1 : c₀₁ = c₁₁ :=
        Option.some.inj (h01.symm.trans h11)
      subst c₁₀
      subst c₁₁
      rfl
    · subst y₁
      have h0 : c₀₀ = c₀₁ :=
        Option.some.inj (h00.symm.trans h01)
      have h1 : c₁₀ = c₁₁ :=
        Option.some.inj (h10.symm.trans h11)
      subst c₀₁
      subst c₁₁
      simp

/-- The three non-singleton vertices a,b,c are in the same E-part. -/
theorem RawDatum.threePlusOne_part_ab
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).part
      (some none) (some (some false)) := rfl

theorem RawDatum.threePlusOne_part_ac
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).part
      (some none) (some (some true)) := rfl

/-- The singleton v lies outside the E-part of a. -/
theorem RawDatum.threePlusOne_cross_va
    (d : RawDatum G C) (c : Option Bool → C) :
    ¬(d.threePlusOneRawPresentation c).part
      none (some none) := by
  simp [threePlusOneRawPresentation]

/-- The three original cross edges from v have EXACT raw labels. -/
theorem RawDatum.threePlusOne_colour_va
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).colour
      none (some none) = some (c none) := rfl

theorem RawDatum.threePlusOne_colour_vb
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).colour
      none (some (some false)) = some (c (some false)) := rfl

theorem RawDatum.threePlusOne_colour_vc
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).colour
      none (some (some true)) = some (c (some true)) := rfl

/-- The effective profile is literally the phi-image of the
independently chosen three original raw cross-edge colours. -/
theorem RawDatum.threePlusOne_effective_va
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).effectiveReduct.F
      none (some none) = d.phi (c none) := by
  exact (d.threePlusOneRawPresentation c).effectiveReduct_crossColour
    none (some none) (c none)
    (d.threePlusOne_colour_va c) |>.symm

theorem RawDatum.threePlusOne_effective_vb
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).effectiveReduct.F
      none (some (some false)) = d.phi (c (some false)) := by
  exact (d.threePlusOneRawPresentation c).effectiveReduct_crossColour
    none (some (some false)) (c (some false))
    (d.threePlusOne_colour_vb c) |>.symm

theorem RawDatum.threePlusOne_effective_vc
    (d : RawDatum G C) (c : Option Bool → C) :
    (d.threePlusOneRawPresentation c).effectiveReduct.F
      none (some (some true)) = d.phi (c (some true)) := by
  exact (d.threePlusOneRawPresentation c).effectiveReduct_crossColour
    none (some (some true)) (c (some true))
    (d.threePlusOne_colour_vc c) |>.symm

end SemigenericEPPA
