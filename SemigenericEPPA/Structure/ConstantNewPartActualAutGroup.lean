import SemigenericEPPA.Structure.ConstantNewPartRawGroupAction
import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup

/-!
# Faithful ACTION in the actual original R1--R3 automorphism group

The regular-class extension supplies a strict group action by raw-
colour-preserving permutations of one enlarged literal rectangle
presentation. We now record that this is a homomorphism into the
ACTUAL subgroup of permutations preserving the complete original
binary language, with both the equivalence relation E and EVERY
raw R_c predicate.

The homomorphism is injective solely because of the new regular
E-class. Thus even if the original action had a kernel, the lifted
finite relative cover group is realized faithfully as actual
automorphisms of a finite original-language structure.

No use of effective G-valued colour preservation alone, and
no post-hoc redefinition of the enlarged raw E relation.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {T : Type t} [Group T]
variable {d : RawDatum G C}

/-- A strict group homomorphism into the literal original
E- and R_c-preserving whole-witness permutation subgroup. -/
def RawRectanglePresentation.adjoinRegularPartRawAutHom
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : T →* Equiv.Perm V)
    (hPart : ∀ (h : T) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : T) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y) :
    T →* binaryRawAutSubgroup
        (fun x y : V ⊕ T =>
          (P.adjoinConstantNewPart (R := T) c0).part x y)
        (fun c x y =>
          (P.adjoinConstantNewPart (R := T) c0).colour x y = some c) := by
  apply binaryRawAutHom
    (fun x y : V ⊕ T =>
      (P.adjoinConstantNewPart (R := T) c0).part x y)
    (fun c x y =>
      (P.adjoinConstantNewPart (R := T) c0).colour x y = some c)
    (sumRawGroupAction rho (rawLeftRegularAction T))
  intro h
  constructor
  · exact sumRawGroupAction_preserves_part
      P c0 rho (rawLeftRegularAction T) hPart h
  · intro c x y
    rw [sumRawGroupAction_preserves_colour
      P c0 rho (rawLeftRegularAction T) hColour h]

/-- The resulting action inside the ACTUAL raw automorphism
group is faithful, even when rho itself is not injective. -/
theorem RawRectanglePresentation.adjoinRegularPartRawAutHom_injective
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : T →* Equiv.Perm V)
    (hPart : ∀ (h : T) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : T) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y) :
    Function.Injective
      (P.adjoinRegularPartRawAutHom c0 rho hPart hColour) := by
  intro a b heq
  apply sumRawGroupAction_regular_injective rho
  exact congrArg Subtype.val heq

/-- Old points are acted on by the original prescribed rho,
not by any recoding of its quotient or effective geometry. -/
theorem RawRectanglePresentation.adjoinRegularPartRawAutHom_old
    (P : RawRectanglePresentation d V)
    (c0 : C)
    (rho : T →* Equiv.Perm V)
    (hPart : ∀ (h : T) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : T) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y)
    (h : T) (x : V) :
    (P.adjoinRegularPartRawAutHom c0 rho hPart hColour h).val
        (.inl x) = .inl (rho h x) :=
  rfl

end SemigenericEPPA
