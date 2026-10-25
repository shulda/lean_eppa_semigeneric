import SemigenericEPPA.Structure.DLFUnrestrictedSemiCoherentClassification
import SemigenericEPPA.Structure.DLFRelationalClassification
import SemigenericEPPA.Bridge.FiniteCanonicalUniverseCoherentClassification

/-!
# Coherent EPPA, unrestricted semi-coherent EP, and actual relational DLF

The complete semi-coherent classification is stated using arbitrary
cofinal families of finite original-raw subgroup-action pairs; the
homogeneous DLF criterion is already expressed in the LITERAL
AllThoseEPPA.Structure (rectangleLanguage C) and its genuine
original E/R_c automorphism group.

Here we explicitly identify the two existing statements and
show that original-relational coherent EPPA implies semi-coherent
EP, hence actual relational DLF. This uses the algebraic
classification, including the exceptional trivial-G branch,
and does NOT assert that coherent and semi-coherent coincide:
the latter requires only ONE complete good congruence orbit.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- Genuine unrestricted finite original-raw semi-coherent
extension property is equivalent to the existence of a
countable homogeneous FULL original-relational R1--R3
structure with dense locally finite full automorphism subgroup. -/
theorem finiteRawSemiCoherentEP_iff_relationalDLF
    (d : RawDatum G C) :
    d.HasFiniteRawSemiCoherentEP ↔
      d.HasCountableRelationalHomogeneousDLF :=
  (d.finiteRawSemiCoherentEP_iff_dlf).trans
    (d.countableRelationalHomogeneousDLF_iff_raw).symm

/-- Coherent EPPA for all finite original E/R_c structures
implies the unrestricted semi-coherent EP property for the
same original finite class. No selected safety condition is
presupposed by the target property. -/
theorem finiteRelationalCoherentEPPA_implies_semiCoherent
    (d : RawDatum G C)
    (hCoherent :
      d.HasFiniteRelationalCoherentEPPAInCanonicalUniverses) :
    d.HasFiniteRawSemiCoherentEP := by
  obtain h :=
    (d.hasFiniteRelationalCoherentEPPAInCanonicalUniverses_iff).mp
      hCoherent
  apply (d.finiteRawSemiCoherentEP_iff).2
  rcases h with hTrivial | ⟨hGood, hSaturated⟩
  · exact Or.inl hTrivial
  · exact Or.inr
      (d.hasCompleteGoodOrbit_of_saturated hSaturated hGood)

/-- In particular coherent EPPA forces the ACTUAL original
relational Fraisse-limit DLF existence criterion. -/
theorem finiteRelationalCoherentEPPA_implies_relationalDLF
    (d : RawDatum G C)
    (hCoherent :
      d.HasFiniteRelationalCoherentEPPAInCanonicalUniverses) :
    d.HasCountableRelationalHomogeneousDLF :=
  (d.finiteRawSemiCoherentEP_iff_relationalDLF).mp
    (d.finiteRelationalCoherentEPPA_implies_semiCoherent hCoherent)

end RawDatum
end SemigenericEPPA
