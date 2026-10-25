import SemigenericEPPA.Examples.FourColourDLFNotCoherent
import SemigenericEPPA.Bridge.SemiCoherentRelationalDLFClassification

/-!
# Concrete strict separation: semi-coherent EP holds, coherent EPPA fails

The fully explicit C₄ datum from `FourColourDLFNotCoherent` has
one complete good congruence orbit but is not congruence saturated.
The certified unrestricted finite-action classification therefore yields
the *genuine* semi-coherent extension property for its original raw age.
The existing negative coherent theorem applies to the same original
E/R_c relational class. No local safety hypothesis occurs in the
statement of semi-coherence.
-/

namespace SemigenericEPPA
namespace FourColourSeparation

/-- The original finite R₁–R₃ class of the explicit C₄ example
has the unrestricted semi-coherent finite subgroup-extension property. -/
theorem semiCoherentEP :
    c4Datum.HasFiniteRawSemiCoherentEP :=
  (c4Datum.finiteRawSemiCoherentEP_iff).2
    (Or.inr hasCompleteGoodOrbit)

/-- The same explicit finite relational class has semi-coherent EP
and DLF, while coherent EPPA fails. This proves that for the
semigeneric rectangle class semi-coherence is strictly weaker
than coherent EPPA, even with nontrivial finite effective G. -/
theorem semiCoherentDLFNotCoherent :
    c4Datum.HasFiniteRawSemiCoherentEP ∧
    c4Datum.HasCountableRelationalHomogeneousDLF ∧
    ¬ c4Datum.HasFiniteRelationalCoherentEPPAInCanonicalUniverses :=
  ⟨semiCoherentEP, relationalDLF, notRelationalCoherentEPPA⟩

end FourColourSeparation
end SemigenericEPPA
