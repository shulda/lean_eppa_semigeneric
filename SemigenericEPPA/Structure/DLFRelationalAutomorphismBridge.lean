import SemigenericEPPA.Structure.DLFCompleteClassification
import SemigenericEPPA.Structure.RelationalRoundtripEquality
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup

/-!
# Full original-relational automorphism subgroup equals full raw Aut

The raw DLF classification is formulated using the convenient
Option-C functional representation, but the mathematical theorem is
about the ORIGINAL AllThoseEPPA binary relational language E,R_c.

Define the full group of genuine permutations preserving and
reflecting every original binary relation on a relational structure A.
For a raw presentation P, its relational interpretation P.toStructure
has exactly P.fullRawAutGroup (as a literally EQUAL subgroup of
Perm(V), not merely an abstractly isomorphic group). For an arbitrary
original relational R1–R3 object A, the canonical raw encoding
h.toRawPresentation has the identical full automorphism subgroup.
No finite-carrier, order, recentering or saturation hypothesis.

Also certify that raw -> relational -> raw preserves the original
Option-C colour function pointwise, not only its some-colour predicates.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- Exact literal original-language automorphism subgroup of A. -/
def relationalFullAutGroup
    (A : Structure (rectangleLanguage C) V) :
    Subgroup (Equiv.Perm V) :=
  binaryRawAutSubgroup (partRel A) (rawRel A)

/-- A raw presentation and its genuine original E/R_c relational
interpretation have EQUAL full automorphism subgroups. -/
theorem RawRectanglePresentation.fullRawAutGroup_eq_relational
    (P : RawRectanglePresentation d V) :
    P.fullRawAutGroup = relationalFullAutGroup P.toStructure := by
  rfl

/-- The converse comparison holds for EVERY original relational
R1–R3 structure, using the certified exact roundtrip equality. -/
theorem IsRectangleStructure.relationalFullAutGroup_eq_raw
    {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) :
    relationalFullAutGroup A =
      h.toRawPresentation.fullRawAutGroup := by
  calc
    relationalFullAutGroup A =
        relationalFullAutGroup h.toRawPresentation.toStructure := by
          rw [h.toRawPresentation_toStructure_eq]
    _ = h.toRawPresentation.fullRawAutGroup := by
          rfl

/-- Raw -> original relational -> canonical raw preserves the FULL
Option-valued colour on every ordered vertex pair. -/
theorem RawRectanglePresentation.toStructure_rawOption_eq
    (P : RawRectanglePresentation d V) (x y : V) :
    P.toStructure_isRectangleStructure.rawOption x y =
      P.colour x y := by
  cases hc : P.colour x y with
  | none =>
      exact (P.toStructure_isRectangleStructure.rawOption_none_iff x y).2
        ((P.colour_none_iff x y).1 hc)
  | some c =>
      exact (P.toStructure_isRectangleStructure.rawOption_some_iff c x y).2 hc

end SemigenericEPPA
