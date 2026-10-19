import SemigenericEPPA.Structure.EffectiveGeometry

/-!
# Restrict effective rectangle geometries to actual vertex subsets

The universal fixed-carrier G=1 action construction works with an
induced old substructure S. We need its effective geometry as an
actual EffectiveGeometry s S, not merely the old E and F restricted
in informal notation.

Both the affine reversal law on cross E-pairs and the exact
noncommutative rectangle constraint are hereditary, so restriction
requires no finiteness, saturation, or choice.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Literal effective E/F subgeometry induced by S subset V. -/
def induced (D : EffectiveGeometry s V) (S : Set V) :
    EffectiveGeometry s S where
  part := {
    r := fun x y => D.part x.val y.val
    iseqv := by
      constructor
      · intro x
        exact D.part.iseqv.refl x.val
      · intro x y hxy
        exact D.part.iseqv.symm hxy
      · intro x y z hxy hyz
        exact D.part.iseqv.trans hxy hyz
  }
  F := fun x y => D.F x.val y.val
  reverse_cross := by
    intro x y hxy
    exact D.reverse_cross x.val y.val hxy
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy hcross
    exact D.rectangle x₀.val x₁.val y₀.val y₁.val
      hx hy hcross

@[simp] theorem induced_part
    (D : EffectiveGeometry s V) (S : Set V) (x y : S) :
    (D.induced S).part x y ↔ D.part x.val y.val :=
  Iff.rfl

@[simp] theorem induced_F
    (D : EffectiveGeometry s V) (S : Set V) (x y : S) :
    (D.induced S).F x y = D.F x.val y.val := rfl

end EffectiveGeometry

end SemigenericEPPA
