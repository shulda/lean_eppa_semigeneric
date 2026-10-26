import SemigenericEPPA.Examples.FourColourSemiCoherentSeparation
import SemigenericEPPA.Bridge.NativeRelationalSemiCoherentConverse

/-!
# The concrete C4 separation, entirely in the native E/R_c API

The already checked raw property is exactly equivalent to the native
unrestricted finite relational semi-coherent extension property.
This bridge turns the example into a direct statement about the same
original finite relational class used for coherent EPPA and DLF.
-/

namespace SemigenericEPPA
namespace FourColourSeparation

/-- One explicit five-raw-colour refinement of C4 has original-language
semi-coherent EP and a full-age homogeneous DLF model, but its finite
original-language class fails coherent EPPA. -/
theorem nativeSemiCoherentDLFNotCoherent :
    c4Datum.HasFiniteRelationalSemiCoherentEP ∧
    c4Datum.HasCountableRelationalHomogeneousDLF ∧
    ¬ c4Datum.HasFiniteRelationalCoherentEPPAInCanonicalUniverses := by
  exact ⟨(c4Datum.finiteRelationalSemiCoherentEP_iff_raw).2 semiCoherentEP,
    relationalDLF, notRelationalCoherentEPPA⟩

end FourColourSeparation
end SemigenericEPPA
