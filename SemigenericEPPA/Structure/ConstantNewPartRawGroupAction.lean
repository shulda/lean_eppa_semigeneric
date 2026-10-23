import SemigenericEPPA.Structure.ConstantNewPartRawRectangle
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

/-!
# Faithful realization of a group as automorphisms via one new E-class

Given any group T acting on an old raw R1--R3 presentation
by permutations preserving the old equivalence relation and
EVERY raw colour, adjoin one new E-class whose carrier is T
itself. All its cross-colours are constant, so the whole action
extends by independent left multiplication on this new class.

The resulting action is a STRICT homomorphism into the full
permutation group of the new original-language raw structure.
It preserves E, all raw colours, and the old action exactly.
It is FAITHFUL regardless of whether the old action was faithful,
because T acts regularly on the new class.

This is the group-action realization step of the finite
relative DLF involution-killing cover. No assumption on
normality, commutativity, s(1), or coherent EPPA is involved.
-/

namespace SemigenericEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {R : Type z}
variable {T : Type t} [Group T]
variable {d : RawDatum G C}

/-- Independent actions of the same group on two summands give
a strict action on their disjoint union. -/
def sumRawGroupAction
    (rho : T →* Equiv.Perm V)
    (lambda : T →* Equiv.Perm R) :
    T →* Equiv.Perm (V ⊕ R) where
  toFun h := Equiv.sumCongr (rho h) (lambda h)
  map_one' := by
    apply Equiv.ext
    intro x
    cases x <;> simp
  map_mul' := by
    intro h k
    apply Equiv.ext
    intro x
    cases x <;> simp [map_mul]

@[simp] theorem sumRawGroupAction_inl
    (rho : T →* Equiv.Perm V)
    (lambda : T →* Equiv.Perm R)
    (h : T) (x : V) :
    sumRawGroupAction rho lambda h (.inl x) = .inl (rho h x) :=
  rfl

@[simp] theorem sumRawGroupAction_inr
    (rho : T →* Equiv.Perm V)
    (lambda : T →* Equiv.Perm R)
    (h : T) (x : R) :
    sumRawGroupAction rho lambda h (.inr x) = .inr (lambda h x) :=
  rfl

/-- A sum action preserves E for the constant new-part raw
presentation exactly when its old action preserves E. -/
theorem sumRawGroupAction_preserves_part
    (P : RawRectanglePresentation d V) (c0 : C)
    (rho : T →* Equiv.Perm V)
    (lambda : T →* Equiv.Perm R)
    (hPart : ∀ (h : T) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (h : T) (x y : V ⊕ R) :
    (P.adjoinConstantNewPart (R := R) c0).part
        (sumRawGroupAction rho lambda h x)
        (sumRawGroupAction rho lambda h y) ↔
      (P.adjoinConstantNewPart (R := R) c0).part x y := by
  cases x <;> cases y <;>
    simp [RawRectanglePresentation.adjoinConstantNewPart,
      constantNewPartRel, hPart]

/-- The same sum action preserves EVERY raw colour in the
actual original-language raw rectangle presentation. -/
theorem sumRawGroupAction_preserves_colour
    (P : RawRectanglePresentation d V) (c0 : C)
    (rho : T →* Equiv.Perm V)
    (lambda : T →* Equiv.Perm R)
    (hColour : ∀ (h : T) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y)
    (h : T) (x y : V ⊕ R) :
    (P.adjoinConstantNewPart (R := R) c0).colour
        (sumRawGroupAction rho lambda h x)
        (sumRawGroupAction rho lambda h y) =
      (P.adjoinConstantNewPart (R := R) c0).colour x y := by
  cases x <;> cases y <;>
    simp [RawRectanglePresentation.adjoinConstantNewPart,
      constantNewPartColour, hColour]

/-- Left multiplication on its own carrier gives a genuine
strict regular action of ANY group T, nonabelian included. -/
def rawLeftRegularAction (T : Type t) [Group T] :
    T →* Equiv.Perm T where
  toFun h := {
    toFun := fun a => h * a
    invFun := fun a => h⁻¹ * a
    left_inv := by intro a; group
    right_inv := by intro a; group }
  map_one' := by
    apply Equiv.ext
    intro a
    simp
  map_mul' := by
    intro h k
    apply Equiv.ext
    intro a
    change (h * k) * a = h * (k * a)
    group

@[simp] theorem rawLeftRegularAction_apply
    (h a : T) :
    rawLeftRegularAction T h a = h * a := rfl

/-- A whole new regular E-class makes the SUM action faithful
even if the action on the prescribed old structure has kernel. -/
theorem sumRawGroupAction_regular_injective
    (rho : T →* Equiv.Perm V) :
    Function.Injective (sumRawGroupAction rho (rawLeftRegularAction T)) := by
  intro h k hEq
  have heq := congrArg
    (fun p : Equiv.Perm (V ⊕ T) => p (.inr (1 : T))) hEq
  have hh : h * (1 : T) = k * (1 : T) :=
    Sum.inr.inj (by simpa only [sumRawGroupAction_inr,
      rawLeftRegularAction_apply] using heq)
  simpa using hh

end SemigenericEPPA
