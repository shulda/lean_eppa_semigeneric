import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup
import SemigenericEPPA.Structure.RawPresentation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-!
# The canonical full finite automorphism group in the original raw language

The finite DLF induction must apply the involution-killing
relative group cover to the actual finite automorphism group of
the finite original-language EPPA witness, not to the auxiliary
effective G-colour permutations.  This module gives the exact
finite subgroup of Perm(V) preserving E and every original R_c.

Option-valued raw colour preservation is equivalent to preservation
of each predicate "colour = some c".  The actual faithful H-action
therefore embeds in this full finite Q, and every individually
constructed raw automorphism is literally an element of Q.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Full automorphism subgroup preserving the literal original
E relation and EVERY raw R_c predicate. -/
abbrev fullRawAutGroup (P : RawRectanglePresentation d V) :
    Subgroup (Equiv.Perm V) :=
  binaryRawAutSubgroup P.part
    (fun c x y => P.colour x y = some c)

/-- Exact original raw E preservation for canonical automorphisms. -/
theorem fullRawAutGroup_part
    (P : RawRectanglePresentation d V)
    (q : P.fullRawAutGroup) (x y : V) :
    P.part (q.val x) (q.val y) ↔ P.part x y :=
  q.property.1 x y

/-- Preservation of ALL raw predicates yields literal equality
of Option-valued raw colours, including non-cross E pairs. -/
theorem fullRawAutGroup_colour
    (P : RawRectanglePresentation d V)
    (q : P.fullRawAutGroup) (x y : V) :
    P.colour (q.val x) (q.val y) = P.colour x y := by
  classical
  cases hL : P.colour (q.val x) (q.val y) with
  | none =>
      cases hR : P.colour x y with
      | none =>
          rfl
      | some c =>
          have hc : P.colour (q.val x) (q.val y) = some c :=
            (q.property.2 c x y).mpr hR
          rw [hL] at hc
          cases hc
  | some c =>
      exact ((q.property.2 c x y).mp hL).symm

/-- The canonical automorphism group of a finite original raw
rectangle is itself finite. -/
theorem finite_fullRawAutGroup
    (P : RawRectanglePresentation d V) [Finite V] :
    Finite P.fullRawAutGroup := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  have hPermFinite : Finite (Equiv.Perm V) :=
    Finite.of_injective
      (fun f : Equiv.Perm V => f.toFun)
      (by
        intro f g he
        exact Equiv.ext (fun x => congrFun he x))
  letI : Finite (Equiv.Perm V) := hPermFinite
  infer_instance

/-- Genuine inclusion of the full raw automorphism group in
all permutations of V, with the usual strict multiplication. -/
def fullRawAutAction
    (P : RawRectanglePresentation d V) :
    P.fullRawAutGroup →* Equiv.Perm V :=
  P.fullRawAutGroup.subtype

/-- A strict H-action preserving E and every raw colour lands
homomorphically in the ACTUAL full original-language group. -/
def fullRawAutHom
    (P : RawRectanglePresentation d V)
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ (h : H) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : H) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y) :
    H →* P.fullRawAutGroup :=
  binaryRawAutHom P.part
    (fun c x y => P.colour x y = some c) rho
    (by
      intro h
      refine ⟨hPart h, ?_⟩
      intro c x y
      change (P.colour (rho h x) (rho h y) = some c) ↔
        (P.colour x y = some c)
      rw [hColour h x y])

/-- Faithfulness is unchanged by embedding into the exact full
original-language automorphism subgroup. -/
theorem fullRawAutHom_injective
    (P : RawRectanglePresentation d V)
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ (h : H) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : H) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y)
    (hFaithful : Function.Injective rho) :
    Function.Injective (P.fullRawAutHom rho hPart hColour) := by
  intro a b hab
  apply hFaithful
  exact congrArg Subtype.val hab

end RawRectanglePresentation
end SemigenericEPPA
