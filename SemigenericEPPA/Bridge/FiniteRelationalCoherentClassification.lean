import SemigenericEPPA.Bridge.FiniteOriginalRelationalSaturatedEPPA
import SemigenericEPPA.Bridge.RelationalTypedCoherentEPPA
import SemigenericEPPA.Bridge.CoherentFiniteRawClassNecessity

/-!
# Original-language coherent EPPA classification for the finite rectangle class

The necessary direction follows from two explicit finite original
raw obstruction gadgets and is already certified for every class
with typed coherent EPPA. The sufficiency has two disjoint branches:
a finite witness for trivial effective G with no good-colour premise,
and the factorial/valuation/raw-cover groupoid witness for general
finite G under genuine good-set nonemptiness and global congruence
saturation.

We phrase the exact biconditional in the ORIGINAL R1--R3 binary
language. The class property quantifies all finite relational
IsRectangleStructure members and permits finite original-language
raw witness presentations. It never replaces E or raw P_c by
only effective F-colour data, and no additional part size or
orientation assumptions are introduced.

The witness type depends on the old structure but its ambient
universe is fixed; its finiteness and true coherent extension
predicate are required. Neither DLF nor SAP follows from this iff.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

/-- For a NONTRIVIAL finite effective group, finite typed coherent
EPPA of every original relational R1–R3 member is equivalent to
the nonempty globally congruence-saturated good set.

For a trivial effective group coherent EPPA is unconditional by the
separate already-certified original relational theorem. We keep
this clean uniform-witness-universe iff in the nontrivial sector,
avoiding an unjustified universe identification in the G=1 branch. -/
theorem RawDatum.finiteRelationalTypedCoherentEPPA_nontrivial_iff
    (d : RawDatum G C) (hNontriv : ¬ Subsingleton G) :
    (∀ (V : Type) [Fintype V]
        (A : Structure (rectangleLanguage C) V),
        IsRectangleStructure d A →
        ∃ (W : Type (max u v))
          (Q : RawRectanglePresentation d W),
          Finite W ∧
          ∃ psi : Structure.Embedding
              (rectangleTrivialAction C) A Q.toStructure,
            Structure.IsCoherentEPPAWitness
              (rectangleTrivialAction C) psi) ↔
      (d.selfReverseEffective.Nonempty ∧
        d.IsCongruenceSaturated) := by
  constructor
  · intro hRel
    have hRaw : ∀ (V : Type) [Fintype V]
        (P : RawRectanglePresentation d V),
        ∃ (W : Type (max u v))
          (Q : RawRectanglePresentation d W)
          (psi : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure),
          Structure.IsCoherentEPPAWitness
            (rectangleTrivialAction C) psi := by
      intro V _ P
      obtain ⟨W, Q, _hFinite, psi, hCoherent⟩ :=
        hRel V P.toStructure P.toStructure_isRectangleStructure
      exact ⟨W, Q, psi, hCoherent⟩
    have hNec :=
      d.necessaryCoherentCondition_of_allFiniteRawPresentations hRaw
    exact hNec.resolve_left hNontriv
  · rintro ⟨hGood, hSat⟩
    intro V _ A hA
    obtain ⟨W, Q, hFinite, psi, hCoherent⟩ :=
      hA.finite_originalCoherentEPPA_of_saturated hGood hSat
    exact ⟨W, Q, hFinite, psi, hCoherent⟩

end SemigenericEPPA
