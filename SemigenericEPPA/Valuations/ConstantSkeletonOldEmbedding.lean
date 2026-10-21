import SemigenericEPPA.Structure.ConstantSkeletonGauge
import SemigenericEPPA.Valuations.OldEmbedding

/-!
# Literal old embedding for the constant-skeleton valuation witness

The canonical old witness injection in OldEmbedding uses the
arbitrary original quotient skeleton K(i,j). The positive coherent
finite-group construction instead needs ONE constant s-fixed
skeleton g0, chosen before any induced subgroup H.

The exact gauge-normal-form lemma of ConstantSkeletonGauge allows
one to change the old embedded vertex valuations while keeping their
real-label and neutral part coordinates unchanged. In the recoded
old zero-section, vertex x has incidence a'(x,j), where a' is
the gauge that absorbs every original K(i,j) into the coordinates.

This proves that the fixed constant-skeleton witness still contains
the entire old effective structure literally and inducedly, without
requiring its original quotient skeleton to be constant. No
coherent automorphism lift or raw-colour completion is claimed here.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- One skeleton of the full two-layer valuation carrier, with the
SAME reversal-fixed effective value on every ordered pair. In
particular its definition does not use a later H-action. -/
def constantEffectiveWitnessSkeleton
    (D : EffectiveGeometry s V)
    (g0 : G) (hfixed : s g0 = g0) :
    EffectiveWitnessSkeleton D where
  colour := fun _ _ => g0
  reverse := by
    intro _ _ _
    exact hfixed.symm

/-- A typed constant-skeleton indexed gauge on the ORIGINAL quotient
sort. The quotient of the reconstructed QuotientGauge's setoid is
definitionally the original quotient, but Lean's typeclass search
does not unfold this fact while looking for a linear order. -/
noncomputable def constantQuotientIndexedGauge
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0) :
    IndexedGauge s V (Quotient D.part) := by
  letI : LinearOrder (Quotient D.toQuotientGauge.part) :=
    (inferInstance : LinearOrder (Quotient D.part))
  exact (IndexedGauge.ofQuotientGauge D.toQuotientGauge).constantSkeletonGauge
    g0 hfixed

/-- The constant-skeleton gauge preserves the actual old effective
cross-part colour, not only the abstract rectangle identity. -/
theorem constantQuotientIndexedGauge_cross
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0)
    (x y : V) (hxy : ¬D.part x y) :
    (D.constantQuotientIndexedGauge g0 hfixed).effective x y =
      D.F x y := by
  letI : LinearOrder (Quotient D.toQuotientGauge.part) :=
    (inferInstance : LinearOrder (Quotient D.part))
  have hi : (IndexedGauge.ofQuotientGauge D.toQuotientGauge).label x ≠
      (IndexedGauge.ofQuotientGauge D.toQuotientGauge).label y := by
    change Quotient.mk D.part x ≠ Quotient.mk D.part y
    intro heq
    exact hxy (Quotient.exact heq)
  calc
    (D.constantQuotientIndexedGauge g0 hfixed).effective x y =
        (IndexedGauge.ofQuotientGauge D.toQuotientGauge).effective x y := by
      exact (IndexedGauge.ofQuotientGauge D.toQuotientGauge).constantSkeletonGauge_cross
        g0 hfixed x y hi
    _ = D.toQuotientGauge.effective x y :=
      IndexedGauge.ofQuotientGauge_effective D.toQuotientGauge x y
    _ = D.F x y := D.quotientGauge_reconstruct_cross x y hxy

/-- A copy of the literal old vertex x in the constant-skeleton
witness. Its part/label are neutral; only its independent target
valuation has been recoded using the constant gauge normal form. -/
noncomputable def constantGaugeOldWitnessVertex
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0) (x : V) :
    EffectiveWitnessVertex D where
  part := oldWitnessPart D x
  old := x
  belongs := rfl
  vertexValuation := fun r =>
    (D.constantQuotientIndexedGauge g0 hfixed).vertexGauge x r.1.1

/-- The revised old embedding is still injective because it
remembers the old real label as its second coordinate. -/
theorem constantGaugeOldWitnessVertex_injective
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0) :
    Function.Injective (D.constantGaugeOldWitnessVertex g0 hfixed) := by
  intro x y h
  exact congrArg (fun X : EffectiveWitnessVertex D => X.old) h

/-- The old copy still induces EXACTLY the original E-equivalence. -/
theorem constantGaugeOldWitnessVertex_part_iff
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0)
    (x y : V) :
    (D.constantEffectiveWitnessSkeleton g0 hfixed).toEffectiveGeometry.part
        (D.constantGaugeOldWitnessVertex g0 hfixed x)
        (D.constantGaugeOldWitnessVertex g0 hfixed y) ↔
      D.part x y := by
  exact ((D.constantEffectiveWitnessSkeleton g0 hfixed).witness_part_iff
    (D.constantGaugeOldWitnessVertex g0 hfixed x)
    (D.constantGaugeOldWitnessVertex g0 hfixed y)).trans
      (D.oldWitnessPart_eq_iff x y)

/-- The exact old combined incidence towards a neutral target
part equals the new constant-skeleton gauge coordinate a'(x,j). -/
theorem constantGaugeOldWitnessVertex_crossIncidence
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0)
    (x y : V)
    (hr : oldWitnessPart D y ≠ oldWitnessPart D x) :
    (D.constantGaugeOldWitnessVertex g0 hfixed x).crossIncidence
      (oldWitnessPart D y) hr =
      (D.constantQuotientIndexedGauge g0 hfixed).vertexGauge x
        (Quotient.mk D.part y) := by
  simp [EffectiveWitnessVertex.crossIncidence,
    constantGaugeOldWitnessVertex, oldWitnessPart,
    distinguishedWitnessPart, neutralPartValuation]

/-- Every original old cross-part effective colour is reproduced
EXACTLY by the one preselected constant-skeleton valuation witness.
The result is not merely an embedding of E-classes or an isomorphism
after an unspecified gauge change. -/
theorem constantGaugeOldWitnessVertex_colour
    (D : EffectiveGeometry s V)
    [LinearOrder (Quotient D.part)]
    (g0 : G) (hfixed : s g0 = g0)
    (x y : V) (hxy : ¬D.part x y) :
    (D.constantEffectiveWitnessSkeleton g0 hfixed).toEffectiveGeometry.F
      (D.constantGaugeOldWitnessVertex g0 hfixed x)
      (D.constantGaugeOldWitnessVertex g0 hfixed y) =
      D.F x y := by
  let R : IndexedGauge s V (Quotient D.part) :=
    D.constantQuotientIndexedGauge g0 hfixed
  let K : EffectiveWitnessSkeleton D :=
    D.constantEffectiveWitnessSkeleton g0 hfixed
  let X : EffectiveWitnessVertex D :=
    D.constantGaugeOldWitnessVertex g0 hfixed x
  let Y : EffectiveWitnessVertex D :=
    D.constantGaugeOldWitnessVertex g0 hfixed y
  have hparts : oldWitnessPart D x ≠ oldWitnessPart D y :=
    D.oldWitnessPart_ne x y hxy
  have hIndex : R.label x ≠ R.label y := by
    change Quotient.mk D.part x ≠ Quotient.mk D.part y
    intro h
    exact hxy (Quotient.exact h)
  have hraw := K.witness_cross_colour X Y hparts
  have hformula : K.toEffectiveGeometry.F X Y =
      gaugeColour s (R.vertexGauge x (Quotient.mk D.part y))
        g0 (R.vertexGauge y (Quotient.mk D.part x)) := by
    change K.toEffectiveGeometry.F X Y =
      gaugeColour s
        (X.crossIncidence (oldWitnessPart D y) hparts.symm)
        (K.colour (oldWitnessPart D x) (oldWitnessPart D y))
        (Y.crossIncidence (oldWitnessPart D x) hparts)
      at hraw
    rw [D.constantGaugeOldWitnessVertex_crossIncidence
          g0 hfixed x y hparts.symm,
        D.constantGaugeOldWitnessVertex_crossIncidence
          g0 hfixed y x hparts] at hraw
    exact hraw
  calc
    K.toEffectiveGeometry.F X Y =
      gaugeColour s (R.vertexGauge x (Quotient.mk D.part y))
        g0 (R.vertexGauge y (Quotient.mk D.part x)) := hformula
    _ = R.effective x y :=
      (R.effective_cross x y hIndex).symm
    _ = D.F x y := D.constantQuotientIndexedGauge_cross g0 hfixed x y hxy

end EffectiveGeometry

end SemigenericEPPA
