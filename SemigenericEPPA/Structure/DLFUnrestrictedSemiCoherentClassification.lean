import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedAgeScheduledTower
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerCountableLimit
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitHomogeneity
import SemigenericEPPA.Structure.DLFCompleteClassification
import SemigenericEPPA.Structure.DLFUniversalAgeTowerFin

/-!
# Full original-raw semi-coherent EP iff actual homogeneous DLF

The semi-coherent extension property quantifies an arbitrary cofinal
SELECTED family of genuine finite E/R_c subgroup actions. Unlike
the special cofinal-safe program, the selected groups are NOT required
to be safe on cross-part involutions.

The direct proof of semi-coherent -> DLF:
* turn the unrestricted selected family into arbitrary finite target
  successors without changing the selection predicate;
* explicitly build an age-cofinal countable tower of actual finite
  subgroup-action pairs with all next-stage partial connectors;
* form its true quotient vertex/group direct limits;
* realize all canonical Fin n original raw presentations inside
  its limit;
* use the faithful full-raw automorphism embedding, next-stage
  connector homogeneity and density, and local finiteness of the
  algebraic colimit.

The converse DLF -> unrestricted semi-coherent EP was independently
certified earlier by the concrete safe family from the DLF criterion.
No Sagi existence theorem is imported or assumed.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- Explicit unrestricted semi-coherent finite group-action family
builds a countable homogeneous full-age original raw rectangle with
an ACTUAL dense locally finite subgroup of its full automorphism
group. No local involution safety assumption on Selected. -/
theorem hasCountableHomogeneousDLF_of_finiteRawSemiCoherentEP
    (d : RawDatum G C)
    (hSemi : d.HasFiniteRawSemiCoherentEP) :
    d.HasCountableHomogeneousDLF := by
  classical
  have hAgeTarget :=
    d.hasAgeTargetSuccessors_of_finiteRawSemiCoherentEP hSemi
  obtain ⟨V, hV, T, hConn, hTargets⟩ :=
    exists_unrestrictedSemiCoherentTower_realizingAgeSchedule
      d hAgeTarget (canonicalFiniteRawTargets (d := d))
  letI : ∀ n, Finite (V n) := hV
  have hFin : ∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → T.VertexLimit,
        Function.Injective e ∧
        (∀ x y : Fin n,
          T.limitRawPresentation.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : Fin n,
          T.limitRawPresentation.colour (e x) (e y) =
            P.colour x y) := by
    intro n P
    obtain ⟨i, hi⟩ :=
      canonicalFiniteRawSchedule_surjective (d := d) ⟨n, P⟩
    have hScheduled :=
      unrestrictedTower_ageSchedule_embedsInLimit
        T (canonicalFiniteRawTargets (d := d)) hTargets i
    dsimp only [canonicalFiniteRawTargets] at hScheduled
    rw [hi] at hScheduled
    obtain ⟨e, he, hp, hc⟩ := hScheduled
    refine ⟨fun x => e (ULift.up x),
      he.comp ULift.up_injective, ?_, ?_⟩
    · intro x y
      simpa only [RawRectanglePresentation.pullbackRaw] using
        hp (ULift.up x) (ULift.up y)
    · intro x y
      simpa only [RawRectanglePresentation.pullbackRaw] using
        hc (ULift.up x) (ULift.up y)
  refine ⟨T.VertexLimit, T.limitRawPresentation,
    T.countable_vertexLimit, hFin, ?_, ?_⟩
  · intro F p hp hPart hColour
    exact T.finiteRawPartialMap_extends_on_limit
      hConn F p hp hPart hColour
  · exact T.exists_actualDenseLocallyFiniteSubgroup_of_connectors
      hConn

/-- The TRUE unrestricted semi-coherent extension property for
the finite raw R1–R3 class is equivalent to the existence of a
countable homogeneous full-age DLF structure. -/
theorem finiteRawSemiCoherentEP_iff_dlf
    (d : RawDatum G C) :
    d.HasFiniteRawSemiCoherentEP ↔
      d.HasCountableHomogeneousDLF := by
  constructor
  · exact d.hasCountableHomogeneousDLF_of_finiteRawSemiCoherentEP
  · exact d.hasFiniteRawSemiCoherentEP_of_dlf

/-- Complete classification of genuine unrestricted semi-coherent
EP: finite effective G is trivial, OR self-reversing raw fibres
contain ONE whole congruence orbit for affine s. This does not
require saturation of all good orbits. -/
theorem finiteRawSemiCoherentEP_iff
    (d : RawDatum G C) :
    d.HasFiniteRawSemiCoherentEP ↔
      Subsingleton G ∨ d.HasCompleteGoodOrbit :=
  (d.finiteRawSemiCoherentEP_iff_dlf).trans
    (d.countableHomogeneousDLF_iff)

end RawDatum
end SemigenericEPPA
