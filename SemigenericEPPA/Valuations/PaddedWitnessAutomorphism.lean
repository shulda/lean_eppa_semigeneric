import SemigenericEPPA.Valuations.PaddedPartialPermutations
import SemigenericEPPA.Structure.PaddedQuotientEquiv
import SemigenericEPPA.Valuations.TwistedPartPermutation
import SemigenericEPPA.Valuations.WitnessSkeleton
import SemigenericEPPA.Valuations.WitnessFiniteness
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual effective witness actions after uniform padding

Combines the previously verified padding, partial E-class permutation,
fibrewise real-label permutation, padded canonical quotient equivalence,
and twisted witness automorphism.  An arbitrary family of twists L
that is trivial on every E-class met by the old partial domain induces
a colour-preserving witness automorphism which sends the **part** and
the **old-label coordinate** of each distinguished source vertex to
their prescribed targets.

This is an actual equivalence of the full finite effective witness,
not merely a hypothetical part map.  Equality of the entire old
witness vertices still requires the compatible prescribed multipliers
and incidence identities (3.14)--(3.19); the result below does NOT
assert the headline EPPA extension theorem.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- For an old partial E-isomorphism, *any* twists that vanish on the
old parts touched by its domain can be incorporated into a genuine
automorphism of a finite effective valuation witness of the padded
geometry.  On each old source vertex, the automorphism has exactly
the requested target old label and neutral witness part.

We explicitly choose an auxiliary linear order on the finite
witness-part sort, which is not part of the relational language.
The theorem deliberately does not claim equality of the full vertex
valuations: that is the outstanding multiplier/incident-coordinate
gate for effective EPPA. -/
theorem exists_paddedWitnessAutomorphism_oldLabelsAndParts
    [Finite V] [Finite G]
    (D : EffectiveGeometry s V)
    (S : Set V) (p : S → V)
    (hp : Function.Injective p)
    (hE : ∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y))
    (L : Quotient D.uniformPaddedGeometry.part →
      (Quotient D.part × V) → G)
    (hL : ∀ (x : S) (z : Quotient D.part × V),
      L (Quotient.mk D.uniformPaddedGeometry.part
        (D.paddedOldMap x.val)) z = 1) :
    ∃ (K : EffectiveWitnessSkeleton D.uniformPaddedGeometry)
      (T : EffectiveWitnessVertex D.uniformPaddedGeometry ≃
        EffectiveWitnessVertex D.uniformPaddedGeometry),
      K.ExtendsOldSkeleton D.uniformPaddedGeometry ∧
      (∀ x : S,
        (T (D.uniformPaddedGeometry.oldWitnessVertex
          (D.paddedOldMap x.val))).old = D.paddedOldMap (p x)) ∧
      (∀ x : S,
        (T (D.uniformPaddedGeometry.oldWitnessVertex
          (D.paddedOldMap x.val))).part =
          oldWitnessPart D.uniformPaddedGeometry (D.paddedOldMap (p x))) ∧
      (∀ X Y : EffectiveWitnessVertex D.uniformPaddedGeometry,
        K.toEffectiveGeometry.part (T X) (T Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ X Y : EffectiveWitnessVertex D.uniformPaddedGeometry,
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (T X) (T Y) =
            K.toEffectiveGeometry.F X Y) := by
  classical
  let B := D.uniformPaddedGeometry
  obtain ⟨ι, π, hπ, _, hpπ⟩ :=
    D.exists_paddedPartAndRealPermutations S p hp hE
  let ιB : Equiv.Perm (Quotient B.part) := D.paddedPartPermutation ι
  have hπB : ∀ z : Quotient D.part × V,
      Quotient.mk B.part (π z) = ιB (Quotient.mk B.part z) := by
    intro z
    exact (D.paddedPartPermutation_class ι π hπ z).symm
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype G := Fintype.ofFinite _
  letI : Finite (Quotient D.part × V) := D.finite_uniformPaddedCarrier
  letI : Fintype (Quotient D.part × V) := Fintype.ofFinite _
  letI : Fintype (EffectiveWitnessPart B) := B.fintypeEffectiveWitnessParts
  letI : LinearOrder (EffectiveWitnessPart B) :=
    LinearOrder.lift' (Fintype.equivFin (EffectiveWitnessPart B))
      (Fintype.equivFin (EffectiveWitnessPart B)).injective
  let K : EffectiveWitnessSkeleton B := B.orderedSkeleton
  let σ : EffectiveWitnessPart B ≃ EffectiveWitnessPart B :=
    twistedWitnessPartPerm B ιB π L
  let ρ : ∀ q : EffectiveWitnessPart B,
      EffectiveWitnessFibre B q ≃ EffectiveWitnessFibre B (σ q) :=
    twistedWitnessFibreEquiv B ιB π L hπB
  let T : EffectiveWitnessVertex B ≃ EffectiveWitnessVertex B :=
    effectiveWitnessAutomorphism B K σ ρ
  have hTpart (X : EffectiveWitnessVertex B) :
      (T X).part = σ X.part :=
    effectiveWitnessAutomorphism_part B K σ ρ X
  have hTold (X : EffectiveWitnessVertex B) :
      (T X).old = π X.old :=
    twistedWitnessAutomorphism_old B K ιB π L hπB X
  have hσ (x : S) :
      σ (oldWitnessPart B (D.paddedOldMap x.val)) =
        oldWitnessPart B (D.paddedOldMap (p x)) := by
    have hcls :
        ιB (Quotient.mk B.part (D.paddedOldMap x.val)) =
          Quotient.mk B.part (D.paddedOldMap (p x)) := by
      calc
        ιB (Quotient.mk B.part (D.paddedOldMap x.val)) =
          Quotient.mk B.part (π (D.paddedOldMap x.val)) :=
            D.paddedPartPermutation_class ι π hπ (D.paddedOldMap x.val)
        _ = Quotient.mk B.part (D.paddedOldMap (p x)) :=
          congrArg (Quotient.mk B.part) (hpπ x)
    have hneutral := twistedWitnessPartPerm_distinguished
      B ιB π L (Quotient.mk B.part (D.paddedOldMap x.val))
      (hL x)
    calc
      σ (oldWitnessPart B (D.paddedOldMap x.val)) =
        distinguishedWitnessPart B
          (ιB (Quotient.mk B.part (D.paddedOldMap x.val))) := hneutral
      _ = oldWitnessPart B (D.paddedOldMap (p x)) :=
        congrArg (distinguishedWitnessPart B) hcls
  refine ⟨K, T, ?_, ?_, ?_, ?_, ?_⟩
  · exact B.orderedSkeleton_extendsOld
  · intro x
    calc
      (T (B.oldWitnessVertex (D.paddedOldMap x.val))).old =
        π (D.paddedOldMap x.val) :=
          hTold (B.oldWitnessVertex (D.paddedOldMap x.val))
      _ = D.paddedOldMap (p x) := hpπ x
  · intro x
    calc
      (T (B.oldWitnessVertex (D.paddedOldMap x.val))).part =
        σ (oldWitnessPart B (D.paddedOldMap x.val)) :=
          hTpart (B.oldWitnessVertex (D.paddedOldMap x.val))
      _ = oldWitnessPart B (D.paddedOldMap (p x)) := hσ x
  · intro X Y
    exact effectiveWitnessAutomorphism_part_iff B K σ ρ X Y
  · intro X Y hXY
    exact effectiveWitnessAutomorphism_colour B K σ ρ X Y hXY

end EffectiveGeometry

end SemigenericEPPA
