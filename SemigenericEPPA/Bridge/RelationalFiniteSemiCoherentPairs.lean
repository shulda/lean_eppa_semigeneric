import SemigenericEPPA.Structure.DLFFiniteUnrestrictedSemiCoherentEP
import SemigenericEPPA.Structure.DLFRelationalAutomorphismBridge

/-!
# Genuine finite original-relational subgroup action pairs

The unrestricted semi-coherent EP classification is currently stated
using finite `RawRectanglePresentation` objects. The data are literally
equivalent to the original finite E/R_c structures, but the language
of the paper is `AllThoseEPPA.Structure (rectangleLanguage C)`.

This module begins a native relational interface. Its finite pair
contains an ACTUAL relational R1–R3 structure and a subgroup of its
literal `relationalFullAutGroup`. We transport such pairs to the
existing raw API, and vice versa, using already certified E/R_c
roundtrips and equality of the two full automorphism subgroups.

No artificial safety certificate is imposed on the subgroup.
The full quantified relational semi-coherent property is a separate
next step, not implicitly asserted by these elementary conversions.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- A finite ORIGINAL R1–R3 relational structure together with
an arbitrary genuine subgroup of its full relational automorphism
group, without any local involution-safety requirement. -/
structure FiniteRelationalActionPair (d : RawDatum G C)
    (V : Type w) [Finite V] where
  rel : Structure (rectangleLanguage C) V
  isRectangle : IsRectangleStructure d rel
  subgroup : Subgroup (relationalFullAutGroup rel)

namespace FiniteRelationalActionPair

variable {V : Type w} [Finite V]

/-- Forget only the relational presentation: retain the original
vertices and transport the literal subgroup via full-Aut equality. -/
noncomputable def toRawActionPair (A : FiniteRelationalActionPair d V) :
    FiniteRawActionPair d V where
  raw := A.isRectangle.toRawPresentation
  subgroup := by
    rw [← A.isRectangle.relationalFullAutGroup_eq_raw]
    exact A.subgroup

/-- Every original E relation survives the conversion exactly. -/
theorem toRawActionPair_part_iff
    (A : FiniteRelationalActionPair d V) (x y : V) :
    A.toRawActionPair.raw.part x y ↔ partRel A.rel x y :=
  Iff.rfl

/-- Every original ordered raw relation is precisely the
corresponding `some c` value of the canonical raw presentation. -/
theorem toRawActionPair_colour_some_iff
    (A : FiniteRelationalActionPair d V) (c : C) (x y : V) :
    A.toRawActionPair.raw.colour x y = some c ↔
      rawRel A.rel c x y :=
  A.isRectangle.rawOption_some_iff c x y

end FiniteRelationalActionPair

namespace FiniteRawActionPair

variable {V : Type w} [Finite V]

/-- Reinterpret a finite raw subgroup action as an ACTUAL finite
relational subgroup action on the same vertex set, retaining E and
every ordered R_c and the literally equal full automorphism group. -/
noncomputable def toRelationalActionPair (A : FiniteRawActionPair d V) :
    FiniteRelationalActionPair d V where
  rel := A.raw.toStructure
  isRectangle := A.raw.toStructure_isRectangleStructure
  subgroup := by
    rw [← A.raw.fullRawAutGroup_eq_relational]
    exact A.subgroup

/-- The original E relation is unchanged by raw-to-relational
conversion. -/
theorem toRelationalActionPair_part_iff
    (A : FiniteRawActionPair d V) (x y : V) :
    partRel A.toRelationalActionPair.rel x y ↔ A.raw.part x y :=
  Iff.rfl

/-- Every ordered original R_c is preserved and reflected. -/
theorem toRelationalActionPair_rawRel_iff
    (A : FiniteRawActionPair d V) (c : C) (x y : V) :
    rawRel A.toRelationalActionPair.rel c x y ↔
      A.raw.colour x y = some c :=
  A.raw.rawRel_toStructure c x y

end FiniteRawActionPair

end SemigenericEPPA
