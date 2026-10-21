import SemigenericEPPA.Valuations.ReferenceIndexedOldSubsetLift
import SemigenericEPPA.Valuations.OldEmbedding
import SemigenericEPPA.Structure.IndexedGauge

/-!
# Old effective E/F embedding for arbitrary literal gauge-zero sections

The relative nontrivial-G H-action uses a selected old zero-section
  x ↦ gaugeOldWitnessVertex(D,a,x),
where a(x,j) is an arbitrary indexed gauge row matrix (not
necessarily the canonical QuotientGauge of D). The witness skeleton
K must match the indexed gauge skeleton on the old *neutral*
witness parts; there is no requirement that the old quotient-gauge
coordinates are definitionally equal to the chosen recoded ones.

This module verifies the zero-section directly. If P is a genuine
indexed gauge on the ACTUAL quotient V/E with
  P.label x = [x]_E,
and its effective F agrees literally with D on cross-E pairs,
then a witness skeleton K extending P.skeleton gives an injective
E-induced map which preserves every old effective cross-E colour.

This is exactly the old effective embedding gate needed for the
fixed-factorial relative H-lift and subsequently coherent EPPA.
No raw-colour statement is claimed here.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- The relative gauge zero-section retains the original old
real-label coordinate, hence is unconditionally injective. -/
theorem gaugeOldWitnessVertex_injective
    (D : EffectiveGeometry s V)
    (a : V → Quotient D.part → G) :
    Function.Injective (D.gaugeOldWitnessVertex a) := by
  intro x y hxy
  exact congrArg (fun X : EffectiveWitnessVertex D => X.old) hxy

/-- The relative gauge zero-section preserves/refects old E
independently of the chosen gauge coordinates and skeleton. -/
theorem gaugeOldWitnessVertex_part_iff
    (D : EffectiveGeometry s V)
    (a : V → Quotient D.part → G)
    (K : EffectiveWitnessSkeleton D)
    (x y : V) :
    K.toEffectiveGeometry.part
      (D.gaugeOldWitnessVertex a x)
      (D.gaugeOldWitnessVertex a y) ↔
        D.part x y := by
  exact (K.witness_part_iff
    (D.gaugeOldWitnessVertex a x)
    (D.gaugeOldWitnessVertex a y)).trans
      (D.oldWitnessPart_eq_iff x y)

/-- Exact old cross-incidence coordinate for any chosen gauge row
matrix a, with no reliance on a canonical anchored presentation. -/
theorem gaugeOldWitnessVertex_crossIncidence
    (D : EffectiveGeometry s V)
    (a : V → Quotient D.part → G)
    (x y : V)
    (hpart : oldWitnessPart D y ≠ oldWitnessPart D x) :
    (D.gaugeOldWitnessVertex a x).crossIncidence
      (oldWitnessPart D y) hpart =
        a x (Quotient.mk D.part y) := by
  simp [EffectiveWitnessVertex.crossIncidence,
    gaugeOldWitnessVertex, oldWitnessPart,
    distinguishedWitnessPart, neutralPartValuation]

/-- When a gauge P presents EXACTLY D's old cross-E data and K
agrees with its skeleton on neutral old parts, the full old
gauge zero-section preserves every literal effective F-colour.
Valid for arbitrary nonabelian groups and affine reversal. -/
theorem gaugeOldWitnessVertex_colour
    (D : EffectiveGeometry s V)
    (P : IndexedGauge s V (Quotient D.part))
    (hLabel : ∀ x : V,
      P.label x = Quotient.mk D.part x)
    (hPF : ∀ x y : V, ¬D.part x y →
      P.effective x y = D.F x y)
    (K : EffectiveWitnessSkeleton D)
    (hK : ∀ i j : Quotient D.part, i ≠ j →
      K.colour (distinguishedWitnessPart D i)
        (distinguishedWitnessPart D j) = P.skeleton i j)
    (x y : V) (hxy : ¬D.part x y) :
    K.toEffectiveGeometry.F
      (D.gaugeOldWitnessVertex P.vertexGauge x)
      (D.gaugeOldWitnessVertex P.vertexGauge y) =
        D.F x y := by
  let X : EffectiveWitnessVertex D :=
    D.gaugeOldWitnessVertex P.vertexGauge x
  let Y : EffectiveWitnessVertex D :=
    D.gaugeOldWitnessVertex P.vertexGauge y
  have hParts : oldWitnessPart D x ≠ oldWitnessPart D y :=
    D.oldWitnessPart_ne x y hxy
  have hIndices : Quotient.mk D.part x ≠ Quotient.mk D.part y := by
    intro heq
    exact hxy (Quotient.exact heq)
  have hCrossP : P.label x ≠ P.label y := by
    rw [hLabel x, hLabel y]
    exact hIndices
  have hRaw := K.witness_cross_colour X Y hParts
  have hFormula :
      K.toEffectiveGeometry.F X Y =
        gaugeColour s
          (P.vertexGauge x (Quotient.mk D.part y))
          (P.skeleton (Quotient.mk D.part x)
            (Quotient.mk D.part y))
          (P.vertexGauge y (Quotient.mk D.part x)) := by
    change K.toEffectiveGeometry.F X Y =
      gaugeColour s
        (X.crossIncidence (oldWitnessPart D y) hParts.symm)
        (K.colour (oldWitnessPart D x) (oldWitnessPart D y))
        (Y.crossIncidence (oldWitnessPart D x) hParts) at hRaw
    rw [D.gaugeOldWitnessVertex_crossIncidence
        P.vertexGauge x y hParts.symm,
      D.gaugeOldWitnessVertex_crossIncidence
        P.vertexGauge y x hParts] at hRaw
    have hSkeleton :
        K.colour (oldWitnessPart D x) (oldWitnessPart D y) =
          P.skeleton (Quotient.mk D.part x)
            (Quotient.mk D.part y) :=
      hK (Quotient.mk D.part x) (Quotient.mk D.part y) hIndices
    rw [hSkeleton] at hRaw
    exact hRaw
  calc
    K.toEffectiveGeometry.F X Y =
        gaugeColour s
          (P.vertexGauge x (Quotient.mk D.part y))
          (P.skeleton (Quotient.mk D.part x)
            (Quotient.mk D.part y))
          (P.vertexGauge y (Quotient.mk D.part x)) := hFormula
    _ = P.effective x y := by
      rw [P.effective_cross x y hCrossP]
      rw [hLabel x, hLabel y]
    _ = D.F x y := hPF x y hxy

end EffectiveGeometry

end SemigenericEPPA
