import SemigenericEPPA.Structure.RawPresentation
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# The three-vertex raw obstruction gadget: a doubleton part and a singleton

The negative coherent-EPPA orbit obstruction starts with the simplest
genuine raw structure having two E-parts: u,v in one part and z in
the other, with the ordered colours from u to z and v to z
prescribed independently.

We represent the vertices by Option Bool: some false=u,
some true=v and none=z. Put both some vertices in one E-class
and the singleton none in the other. Given ANY two raw colours
c₀,c₁∈C, assign them to (u,z) and (v,z), with reverse colours
on oppositely ordered cross edges and no colours inside a part.

No rectangle constraint can fail, because every cross-part
rectangle has one repeated row or one repeated column. The
construction works for ANY possibly nonabelian group, affine
anti-involution, finite or infinite raw alphabet, and also empty
or non-self-reversing raw-colour sets.

The NEXT gate takes c₀=self-reversing, obtains c₁ from surjectivity
over a*g, and builds the actual old partial transposition u↔z.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- Actual original raw rectangle data on the three vertices
`some false`, `some true`, `none`, in E-parts of sizes 2,1. -/
noncomputable def RawDatum.twoPlusOneRawPresentation
    (d : RawDatum G C) (c : Bool → C) :
    RawRectanglePresentation d (Option Bool) where
  part := fun x y => x.isSome = y.isSome
  part_equiv := by
    constructor
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz
  colour := fun x y =>
    match x, y with
    | some b, none => some (c b)
    | none, some b => some (d.reverse (c b))
    | _, _ => none
  colour_none_iff := by
    intro x y
    cases x <;> cases y <;> simp
  colour_reverse := by
    intro x y
    cases x <;> cases y <;> simp [d.reverse_involutive]
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    have hrepeat : x₀ = x₁ ∨ y₀ = y₁ := by
      cases x₀ <;> cases x₁ <;>
        cases y₀ <;> cases y₁ <;>
        simp_all
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

/-- u and v are in one E-part. -/
theorem RawDatum.twoPlusOne_part_uv
    (d : RawDatum G C) (c : Bool → C) :
    (d.twoPlusOneRawPresentation c).part
      (some false) (some true) := rfl

/-- z is outside the E-part of u. -/
theorem RawDatum.twoPlusOne_cross_uz
    (d : RawDatum G C) (c : Bool → C) :
    ¬(d.twoPlusOneRawPresentation c).part
      (some false) none := by
  simp [twoPlusOneRawPresentation]

/-- The first old directed cross-edge has exactly colour c(false). -/
theorem RawDatum.twoPlusOne_colour_uz
    (d : RawDatum G C) (c : Bool → C) :
    (d.twoPlusOneRawPresentation c).colour
      (some false) none = some (c false) := rfl

/-- The second old directed cross-edge has exactly colour c(true). -/
theorem RawDatum.twoPlusOne_colour_vz
    (d : RawDatum G C) (c : Bool → C) :
    (d.twoPlusOneRawPresentation c).colour
      (some true) none = some (c true) := rfl

/-- The first prescribed raw colour determines precisely
its effective group colour, with no additional constraints. -/
theorem RawDatum.twoPlusOne_effective_uz
    (d : RawDatum G C) (c : Bool → C) :
    (d.twoPlusOneRawPresentation c).effectiveReduct.F
      (some false) none = d.phi (c false) := by
  exact (d.twoPlusOneRawPresentation c).effectiveReduct_crossColour
    (some false) none (c false)
    (d.twoPlusOne_colour_uz c) |>.symm

/-- Likewise for the second old directed cross-edge. -/
theorem RawDatum.twoPlusOne_effective_vz
    (d : RawDatum G C) (c : Bool → C) :
    (d.twoPlusOneRawPresentation c).effectiveReduct.F
      (some true) none = d.phi (c true) := by
  exact (d.twoPlusOneRawPresentation c).effectiveReduct_crossColour
    (some true) none (c true)
    (d.twoPlusOne_colour_vz c) |>.symm

end SemigenericEPPA
