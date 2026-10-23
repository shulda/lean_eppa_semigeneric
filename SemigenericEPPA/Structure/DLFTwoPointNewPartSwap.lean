import SemigenericEPPA.Structure.ConstantNewPartRawGroupAction
import SemigenericEPPA.Structure.RawPresentation
import Mathlib.GroupTheory.Perm.Basic

/-!
# The two-point new E-class with an actual transposition automorphism

The final parity contradiction in the negative DLF argument
starts with ANY finite raw R1--R3 structure P, adjoins one new
E-class consisting of two points, and demands the partial swap
of these points be extended by an element of a finite group.
That extension element has even order, and therefore forces a
nontrivial involution in that finite group by Cauchy's theorem.

The new E-class construction itself is already certified:
P.adjoinConstantNewPart (R := Bool) c0 assigns constant raw
colours on its cross-pairs and preserves every old raw colour.
We isolate an EXPLICIT automorphism that fixes every old vertex
and exchanges the two distinct new vertices, preserving E and
all original raw relations literally.

This module does NOT yet formalize Cauchy's theorem, extension
of the swap through an arbitrary finite semi-coherent pair, or
the global negative DLF conclusion.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

/-- Literal permutation of V⊕Bool which fixes old vertices and
exchanges the two new vertices of the additional E-class. -/
def twoPointNewPartSwap : Equiv.Perm (V ⊕ Bool) :=
  Equiv.sumCongr (Equiv.refl V) (Equiv.swap false true)

@[simp] theorem twoPointNewPartSwap_old (x : V) :
    (twoPointNewPartSwap (V := V)) (.inl x) = .inl x := rfl

@[simp] theorem twoPointNewPartSwap_false :
    (twoPointNewPartSwap (V := V)) (.inr false) = .inr true := by
  simp [twoPointNewPartSwap]

@[simp] theorem twoPointNewPartSwap_true :
    (twoPointNewPartSwap (V := V)) (.inr true) = .inr false := by
  simp [twoPointNewPartSwap]

/-- The two fresh vertices lie in the SAME newly added E-class. -/
theorem RawRectanglePresentation.twoPointNewPart_sameClass
    (P : RawRectanglePresentation d V) (c0 : C) :
    (P.adjoinConstantNewPart (R := Bool) c0).part
      (.inr false) (.inr true) := trivial

/-- The transposition preserves and reflects all E-relations,
including the exact old E-structure. -/
theorem RawRectanglePresentation.twoPointNewPartSwap_part
    (P : RawRectanglePresentation d V) (c0 : C)
    (x y : V ⊕ Bool) :
    (P.adjoinConstantNewPart (R := Bool) c0).part
        (twoPointNewPartSwap x) (twoPointNewPartSwap y) ↔
      (P.adjoinConstantNewPart (R := Bool) c0).part x y := by
  cases x <;> cases y <;>
    simp [twoPointNewPartSwap,
      RawRectanglePresentation.adjoinConstantNewPart, constantNewPartRel]

/-- The swap preserves each literal Option-valued raw colour
of the enlarged original R1--R3 rectangle. -/
theorem RawRectanglePresentation.twoPointNewPartSwap_colour
    (P : RawRectanglePresentation d V) (c0 : C)
    (x y : V ⊕ Bool) :
    (P.adjoinConstantNewPart (R := Bool) c0).colour
        (twoPointNewPartSwap x) (twoPointNewPartSwap y) =
      (P.adjoinConstantNewPart (R := Bool) c0).colour x y := by
  cases x <;> cases y <;>
    simp [twoPointNewPartSwap,
      RawRectanglePresentation.adjoinConstantNewPart, constantNewPartColour]

/-- Hence the actual involutive transposition is an
automorphism of the entire original binary language E+R_c. -/
theorem RawRectanglePresentation.twoPointNewPartSwap_rawRel
    (P : RawRectanglePresentation d V) (c0 : C)
    (c : C) (x y : V ⊕ Bool) :
    rawRel (P.adjoinConstantNewPart (R := Bool) c0).toStructure c
        (twoPointNewPartSwap x) (twoPointNewPartSwap y) ↔
      rawRel (P.adjoinConstantNewPart (R := Bool) c0).toStructure c
        x y := by
  change
    (P.adjoinConstantNewPart (R := Bool) c0).colour
        (twoPointNewPartSwap x) (twoPointNewPartSwap y) = some c ↔
      (P.adjoinConstantNewPart (R := Bool) c0).colour x y = some c
  rw [P.twoPointNewPartSwap_colour c0 x y]

/-- The two fresh vertices are distinct, and the explicit
new-part automorphism exchanges them in both directions. -/
theorem RawRectanglePresentation.twoPointNewPart_transposition
    (P : RawRectanglePresentation d V) (c0 : C) :
    ((Sum.inr false : V ⊕ Bool) ≠ .inr true) ∧
      twoPointNewPartSwap (.inr false : V ⊕ Bool) = .inr true ∧
      twoPointNewPartSwap (.inr true : V ⊕ Bool) = .inr false := by
  simp

end SemigenericEPPA
