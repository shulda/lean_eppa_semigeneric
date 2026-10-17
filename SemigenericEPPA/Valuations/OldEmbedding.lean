import SemigenericEPPA.Valuations.EffectiveCarrier

/-!
# Exact old embedding into the effective EPPA valuation carrier

The witness parts have two coordinates (i,h), and witness vertices
have an independent valuation χ toward every other witness part.
The canonical old copy uses neutral h≡1 and the old canonical
quotient gauge coordinates.

Assume the witness skeleton agrees with the original quotient
skeleton on pairs of distinguished (neutral) witness parts.
Then the map x ↦ oldWitnessVertex x is injective, reflects and
preserves E, and preserves EVERY cross-part effective group colour.
In particular this checks the embedding calculation (3.7)--(3.8)
with the target-part valuation convention of (3.5).

This is an embedding of EFFECTIVE geometries. The global EPPA
extension of partial automorphisms and the raw-fibre lift remain open.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Exact skeleton agreement on the neutral witness part copies of
old E-classes, as required by (3.4) in the manuscript. -/
def EffectiveWitnessSkeleton.ExtendsOldSkeleton
    (D : EffectiveGeometry s V) (K : EffectiveWitnessSkeleton D) : Prop :=
  ∀ i j : Quotient D.part, i ≠ j →
    K.colour (distinguishedWitnessPart D i)
      (distinguishedWitnessPart D j) =
        D.toQuotientGauge.skeleton i j

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- The two distinguished witness parts coincide precisely when
the corresponding old vertices are in the same E-class. -/
theorem oldWitnessPart_eq_iff (x y : V) :
    oldWitnessPart D x = oldWitnessPart D y ↔ D.part x y := by
  constructor
  · intro h
    have heq : Quotient.mk D.part x = Quotient.mk D.part y :=
      congrArg (fun q : EffectiveWitnessPart D => q.1) h
    exact Quotient.exact heq
  · intro h
    exact congrArg (distinguishedWitnessPart D) (Quotient.sound h)

/-- The E-relation is reflected AND preserved by the old inclusion
in an effective witness built from an arbitrary skeleton. -/
theorem oldWitnessVertex_part_iff
    (K : EffectiveWitnessSkeleton D) (x y : V) :
    K.toEffectiveGeometry.part (D.oldWitnessVertex x)
        (D.oldWitnessVertex y) ↔ D.part x y := by
  exact (K.witness_part_iff
      (D.oldWitnessVertex x) (D.oldWitnessVertex y)).trans
    (D.oldWitnessPart_eq_iff x y)

/-- The only skeleton condition needed for the old effective copy is
agreement of K with the original skeleton on neutral witness parts. -/
theorem oldWitnessVertex_colour
    (K : EffectiveWitnessSkeleton D)
    (hK : K.ExtendsOldSkeleton D)
    (x y : V) (hxy : ¬D.part x y) :
    K.toEffectiveGeometry.F (D.oldWitnessVertex x)
      (D.oldWitnessVertex y) = D.F x y := by
  have hpart :
      oldWitnessPart D x ≠ oldWitnessPart D y :=
    D.oldWitnessPart_ne x y hxy
  have hclasses :
      (Quotient.mk D.part x) ≠ (Quotient.mk D.part y) := by
    intro h
    exact hxy (Quotient.exact h)
  have hraw := K.witness_cross_colour
      (D.oldWitnessVertex x) (D.oldWitnessVertex y) hpart
  have hformula :
      K.toEffectiveGeometry.F (D.oldWitnessVertex x)
          (D.oldWitnessVertex y) =
        gaugeColour s
          (D.toQuotientGauge.vertexGauge x (Quotient.mk D.part y))
          (D.toQuotientGauge.skeleton
            (Quotient.mk D.part x) (Quotient.mk D.part y))
          (D.toQuotientGauge.vertexGauge y (Quotient.mk D.part x)) := by
    change K.toEffectiveGeometry.F (D.oldWitnessVertex x)
        (D.oldWitnessVertex y) =
      gaugeColour s
        ((D.oldWitnessVertex x).crossIncidence
          (oldWitnessPart D y) hpart.symm)
        (K.colour (oldWitnessPart D x) (oldWitnessPart D y))
        ((D.oldWitnessVertex y).crossIncidence
          (oldWitnessPart D x) hpart) at hraw
    rw [D.oldWitnessVertex_crossIncidence x y hpart.symm,
      D.oldWitnessVertex_crossIncidence y x hpart,
      hK (Quotient.mk D.part x) (Quotient.mk D.part y) hclasses] at hraw
    exact hraw
  calc
    K.toEffectiveGeometry.F (D.oldWitnessVertex x)
        (D.oldWitnessVertex y) =
      gaugeColour s
        (D.toQuotientGauge.vertexGauge x (Quotient.mk D.part y))
        (D.toQuotientGauge.skeleton
          (Quotient.mk D.part x) (Quotient.mk D.part y))
        (D.toQuotientGauge.vertexGauge y (Quotient.mk D.part x)) := hformula
    _ = D.toQuotientGauge.toEffectiveGeometry.F x y := by
      exact (D.toQuotientGauge.effective_cross x y hxy).symm
    _ = D.F x y := D.quotientGauge_reconstruct_cross x y hxy

end EffectiveGeometry
end SemigenericEPPA
