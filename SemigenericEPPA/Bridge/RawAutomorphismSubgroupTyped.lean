import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup
import SemigenericEPPA.Bridge.RawTypedAutomorphism
import SemigenericEPPA.Bridge.RawTypedEPPA

/-!
# Convert the genuine raw automorphism subgroup to typed automorphisms

For coherent EPPA, the groupoid conjugation is most naturally
performed inside the genuine group of E- and all P_c-preserving
permutations of the final raw-cover carrier. The upstream
AllThoseEPPA statement, however, requires actual
Structure.Automorphism values in the literal binary language.

The certified binaryRawAutSubgroup already supplies each E and P_c
preservation equivalence. Raw presentations have EXACTLY one colour
on every cross E-pair and none inside E. We therefore recover
equality of their Option-valued colour functions and apply the
previously certified typed-automorphism constructor.

Conversion preserves the identity and strict multiplication
(composition), so the exact groupoid functor built in the subgroup
translates without weakening or hidden language permutations.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v}
variable {W : Type w} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The actual group of E- and raw-P_c-preserving automorphisms of
the complete literal rectangle presentation Q. -/
abbrev actualRawAutomorphismGroup (Q : RawRectanglePresentation d W) :=
  binaryRawAutSubgroup Q.part
    (fun c x y => Q.colour x y = some c)

/-- A genuine binary raw-relational automorphism preserves the
TOTAL Option-valued colour function, including the none case. -/
theorem actualRawAutomorphism_colour
    (Q : RawRectanglePresentation d W)
    (g : actualRawAutomorphismGroup Q) (x y : W) :
    Q.colour (g.val x) (g.val y) = Q.colour x y := by
  have he := g.property.1 x y
  cases hc : Q.colour x y with
  | none =>
      have hpart : Q.part x y := (Q.colour_none_iff x y).mp hc
      have hpart' : Q.part (g.val x) (g.val y) :=
        he.mpr hpart
      exact (Q.colour_none_iff (g.val x) (g.val y)).mpr hpart'
  | some c =>
      exact (g.property.2 c x y).mpr hc

/-- Turn a *certified raw automorphism* into one of the actual
upstream typed Automorphism values, with identity language action. -/
def actualRawAutomorphism_toTyped
    (Q : RawRectanglePresentation d W)
    (g : actualRawAutomorphismGroup Q) :
    Structure.Automorphism (rectangleTrivialAction C) Q.toStructure :=
  Q.toTypedAutomorphism g.val
    g.property.1 (Q.actualRawAutomorphism_colour g)

@[simp] theorem actualRawAutomorphism_toTyped_apply
    (Q : RawRectanglePresentation d W)
    (g : actualRawAutomorphismGroup Q)
    (x : W) :
    Q.actualRawAutomorphism_toTyped g x = g.val x := by
  rfl

/-- A genuine automorphism subgroup identity maps to the typed
whole-structure identity, not an arbitrary extension of the
empty partial map. -/
theorem actualRawAutomorphism_toTyped_one
    (Q : RawRectanglePresentation d W) :
    Q.actualRawAutomorphism_toTyped 1 =
      Structure.Automorphism.id
        (rectangleTrivialAction C) Q.toStructure := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    rfl

/-- The typed conversion strictly respects group multiplication
and the upstream automorphism composition convention. -/
theorem actualRawAutomorphism_toTyped_mul
    (Q : RawRectanglePresentation d W)
    (g h : actualRawAutomorphismGroup Q) :
    Q.actualRawAutomorphism_toTyped (g * h) =
      (Q.actualRawAutomorphism_toTyped g).comp
        (Q.actualRawAutomorphism_toTyped h) := by
  apply Structure.Automorphism.ext_of_lang_apply
  · rfl
  · intro x
    rfl

end RawRectanglePresentation

end SemigenericEPPA
