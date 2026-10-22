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

/-- Entire finite raw R1--R3 class has typed coherent EPPA exactly
when G is trivial, or the set of truly self-reversing effective
colours is nonempty and a union of complete congruence orbits.

The fixed witness universe can be selected uniformly large
enough for every finite old carrier in Type 0. -/
theorem RawDatum.finiteRawTypedCoherentEPPA_iff
    (d : RawDatum G C) :
    (∀ (V : Type) [Fintype V]
        (P : RawRectanglePresentation d V),
        ∃ (W : Type (max u v))
          (Q : RawRectanglePresentation d W)
          (psi : Structure.Embedding (rectangleTrivialAction C)
            P.toStructure Q.toStructure),
          Structure.IsCoherentEPPAWitness (rectangleTrivialAction C) psi) ↔
    (Subsingleton G ∨
      (d.selfReverseEffective.Nonempty ∧
        d.IsCongruenceSaturated)) := by
  constructor
  · intro hEPPA
    exact d.necessaryCoherentCondition_of_allFiniteRawPresentations
      hEPPA
  · rintro (hTriv | ⟨hGood, hSat⟩)
    · letI : Subsingleton G := hTriv
      intro V _ P
      obtain ⟨_hFinite, Q, psi, hCoherent⟩ :=
        P.finite_typedCoherentEPPA_witness
      exact ⟨GOneJointRawCarrier P, Q, psi, hCoherent⟩
    · intro V _ P
      obtain ⟨_j, Q, _R, K, J, _hFinite, psi, hCoherent⟩ :=
        P.finite_typedCoherentEPPA_witness_of_saturated hGood hSat
      exact ⟨RawCoverVertex
          (EffectiveWitnessVertex Q.toEffectiveGeometry)
          (UniversalResidualCarrier C),
        rawCoverPresentation K.toEffectiveGeometry
          J.code J.baseline J.baseline_reverse,
        psi, hCoherent⟩

end SemigenericEPPA
