import SemigenericEPPA.Bridge.ExactRawPartialGroupoid
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual automorphism groups of induced raw substructures

The exact partial raw groupoid provides arrows S→T. Its endomorphisms
S→S are precisely the genuine raw-colour-preserving permutations of
S and form a group under exact composition. This is the correct
stabilizer H=Aut(P|S) in the C0 coherent-EPPA assembly.

We construct its strict evaluation homomorphism into Perm(S),
verify preservation of the original E and all literal raw colours,
and prove the group is finite when the original old carrier is
finite. These are the exact premises needed to instantiate the
certified G=1 factorial-safe H-action theorem on every induced S.

No coherent functor or groupoid representatives are yet selected.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {A : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation.ExactPartialIso

/-- Actual colour-preserving automorphisms of an induced old subset
form a group. Multiplication is composition (right map first). -/
instance (P : RawRectanglePresentation d A) (S : Set A) :
    Group (ExactPartialIso P S S) where
  mul := fun f g => f.comp g
  one := refl P S
  inv := symm
  mul_assoc := by
    intro f g h
    exact comp_assoc h g f
  one_mul := by
    intro f
    exact refl_comp f
  mul_one := by
    intro f
    exact comp_refl f
  inv_mul_cancel := by
    intro f
    exact symm_comp f

/-- Strict evaluation of the induced raw automorphism group on
the original vertices of S, with no additional group choice. -/
def autAction
    (P : RawRectanglePresentation d A) (S : Set A) :
    ExactPartialIso P S S →* Equiv.Perm S where
  toFun := fun f => f.toEquiv
  map_one' := by
    apply Equiv.ext
    intro x
    rfl
  map_mul' := by
    intro f g
    apply Equiv.ext
    intro x
    rfl

/-- Exact E preservation by every element of the actual raw
automorphism group, in the orientation required by H-action APIs. -/
theorem autAction_part
    (P : RawRectanglePresentation d A) (S : Set A)
    (h : ExactPartialIso P S S) (x y : S) :
    P.part x.val y.val ↔
      P.part ((autAction P S h) x).val
        ((autAction P S h) y).val :=
  (h.part_iff x y).symm

/-- Exact preservation of every ordered raw colour, including
same-part None, by the canonical induced raw automorphism action. -/
theorem autAction_colour
    (P : RawRectanglePresentation d A) (S : Set A)
    (h : ExactPartialIso P S S) (x y : S) :
    P.colour ((autAction P S h) x).val
      ((autAction P S h) y).val =
        P.colour x.val y.val :=
  h.colour_eq x y

/-- Actual automorphism groups of induced substructures of finite
old structures are finite, not just pointwise permutation groups. -/
theorem finite_exactRawAutomorphismGroup
    [Finite A] (P : RawRectanglePresentation d A)
    (S : Set A) :
    Finite (ExactPartialIso P S S) := by
  classical
  letI : Finite S := inferInstance
  exact Finite.of_injective
    (fun f : ExactPartialIso P S S => f.toEquiv)
    (fun f g heq => ext f g heq)

end RawRectanglePresentation.ExactPartialIso

end SemigenericEPPA
