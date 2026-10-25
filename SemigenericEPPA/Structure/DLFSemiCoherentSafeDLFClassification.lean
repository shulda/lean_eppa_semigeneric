import SemigenericEPPA.Structure.DLFSemiCoherentSafeAgeScheduledTower
import SemigenericEPPA.Structure.DLFCompleteClassification
import SemigenericEPPA.Structure.DLFUniversalAgeTowerFin
import SemigenericEPPA.Structure.DLFTrivialSafePairSeed

/-!
# DLF iff cofinal finite safe-pair semi-coherent group extensions

The explicitly defined cofinal safe finite original-raw group
extension property provides an actual countable tower containing
every finite original age target, and extending all old finite
partial isomorphisms through a strict finite group action.

The previously certified direct-limit machinery then constructs
a countable homogeneous original raw R1--R3 presentation with
the FULL finite age and one dense locally finite subgroup of
its genuine full raw automorphism group.

Conversely, our independently CI-certified DLF iff implies
the algebraic condition G=1 or one complete good affine orbit;
each case already produces the concrete cofinal safe finite
group extension family. Hence a three-way iff among:
* the concrete safe-pair semi-coherent finite extension property,
* existence of an actual homogeneous full-age DLF raw model,
* the algebraic criterion G=1 or one complete good orbit.

This is a semigeneric-specific direct construction, NOT the
general theorem of Sagi for arbitrary Fraisse classes and not
a classification of all possible (possibly unsafe) cofinal
families as safe. No external Fraisse existence axiom is used.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- Build the true countable homogeneous R1--R3 DLF witness
directly from the abstract finite safe-pair cofinal family
property, with NO good-orbit or trivial-G hypothesis here. -/
theorem hasCountableHomogeneousDLF_of_cofinalSafeFiniteGroupExtension
    (d : RawDatum G C)
    (hSafe : d.HasCofinalSafeFiniteGroupExtension) :
    d.HasCountableHomogeneousDLF := by
  classical
  let A₀ : FiniteSafePairState d := {
    carrier := ULift.{max u v} (Fin 0)
    finite_carrier := inferInstance
    pair := ((emptyFiniteRaw (d := d)).pullbackRaw ULift.down).trivialSafePair
  }
  obtain ⟨V, hV, T, hConn, _hStart, hTargets⟩ :=
    exists_safeFamily_safeTower_realizingAgeSchedule hSafe A₀
      (canonicalFiniteRawTargets (d := d))
  letI : ∀ n, Finite (V n) := hV
  refine ⟨T.VertexLimit, T.limitRawPresentation,
    T.countable_vertexLimit, ?_, ?_, ?_⟩
  · exact universalAgeFin_of_canonicalSchedule T hTargets
  · intro F p hp hPart hColour
    exact T.finiteRawPartialMap_extends_on_limit
      hConn F p hp hPart hColour
  · exact T.exists_actualDenseLocallyFiniteSubgroup_of_connectors hConn

/-- The selected finite cofinal safe-pair semi-coherent property
is equivalent to true countable homogeneous DLF in the original
raw language for this semigeneric rectangle class. -/
theorem cofinalSafeFiniteGroupExtension_iff_dlf
    (d : RawDatum G C) :
    d.HasCofinalSafeFiniteGroupExtension ↔
      d.HasCountableHomogeneousDLF := by
  constructor
  · exact d.hasCountableHomogeneousDLF_of_cofinalSafeFiniteGroupExtension
  · intro hDLF
    exact d.hasCofinalSafeFiniteGroupExtension_of_dlfCriterion
      ((d.countableHomogeneousDLF_iff).mp hDLF)

/-- Consequently the concrete cofinal finite safe-pair
semi-coherent extension property has precisely the same
algebraic classification as DLF: trivial effective G or
one complete good affine congruence orbit. -/
theorem cofinalSafeFiniteGroupExtension_iff
    (d : RawDatum G C) :
    d.HasCofinalSafeFiniteGroupExtension ↔
      Subsingleton G ∨ d.HasCompleteGoodOrbit :=
  (d.cofinalSafeFiniteGroupExtension_iff_dlf).trans
    (d.countableHomogeneousDLF_iff)

end RawDatum
end SemigenericEPPA
