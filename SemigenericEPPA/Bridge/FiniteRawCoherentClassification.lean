import SemigenericEPPA.Bridge.NontrivialSaturatedTypedCoherentEPPA
import SemigenericEPPA.Bridge.GOneTypedCoherentEPPA
import SemigenericEPPA.Bridge.CoherentFiniteRawClassNecessity

/-!
# Exact coherent-EPPA classification for the finite raw rectangle class

The 2+1 and 3+1 original raw obstruction gadgets already prove the
necessary algebraic criterion for coherent EPPA of the entire class:
either G is subsingleton, or the good self-reversing effective set
is nonempty and globally congruence-saturated.

The trivial-group positive theorem constructs finite original-language
coherent EPPA witnesses unconditionally. The new nontrivial-G positive
theorem constructs such finite witnesses whenever the good effective
set is nonempty and globally saturated, using one globally fixed
factorial valuation and raw cover for both individual connectors
and all induced automorphism group homomorphisms.

Combining them proves the finite-class classification, with no
Ramsey or DLF conclusions. All witnesses are typed original R1--R3
binary relational structures. This file is only a corollary;
the hard positive construction is in the imported theorem and
MUST pass complete CI and axiom auditing before being counted.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

/-- For a NONTRIVIAL finite effective group, finite typed coherent EPPA
for all original R1–R3 raw members in one fixed sufficiently large
universe is equivalent to the genuine good-effective-colour set being
nonempty and globally congruence-saturated.

The trivial-G case is covered independently by
`finite_typedCoherentEPPA_witness`. Its smaller witness type
universe is not silently identified with a larger one here. -/
theorem RawDatum.finiteRawTypedCoherentEPPA_nontrivial_iff
    (d : RawDatum G C) (hNontriv : ¬ Subsingleton G) :
    (∀ (V : Type) [Fintype V]
        (P : RawRectanglePresentation d V),
        ∃ (W : Type (max u v))
          (Q : RawRectanglePresentation d W),
          Finite W ∧
          ∃ psi : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure,
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) psi) ↔
      (d.selfReverseEffective.Nonempty ∧
        d.IsCongruenceSaturated) := by
  constructor
  · intro hEPPA
    have hRaw : ∀ (V : Type) [Fintype V]
        (P : RawRectanglePresentation d V),
        ∃ (W : Type (max u v))
          (Q : RawRectanglePresentation d W)
          (psi : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure),
          Structure.IsCoherentEPPAWitness
            (rectangleTrivialAction C) psi := by
      intro V _ P
      obtain ⟨W, Q, _hFinite, psi, hCoherent⟩ := hEPPA V P
      exact ⟨W, Q, psi, hCoherent⟩
    have hNec :=
      d.necessaryCoherentCondition_of_allFiniteRawPresentations hRaw
    exact hNec.resolve_left hNontriv
  · rintro ⟨hGood, hSat⟩
    intro V _ P
    obtain ⟨_j, Q, _R, K, J, hFinite, psi, hCoherent⟩ :=
      P.finite_typedCoherentEPPA_witness_of_saturated hGood hSat
    exact ⟨RawCoverVertex
        (EffectiveWitnessVertex Q.toEffectiveGeometry)
        (UniversalResidualCarrier C),
      rawCoverPresentation K.toEffectiveGeometry
        J.code J.baseline J.baseline_reverse,
      hFinite, psi, hCoherent⟩

end SemigenericEPPA
