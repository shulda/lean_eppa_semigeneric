import SemigenericEPPA.Structure.UniformPadding
import SemigenericEPPA.Valuations.EffectiveCarrier

/-!
# Normalized diagonal gauge in the effective E0 padding

The manuscript explicitly sets a_(x,i)=1 when i is x's own
E-part. This matters even though the corresponding group-valued
edge is not a cross-part colour: a blown-up witness part (i,h) can
be different from the distinguished part (i,1), and the valuation
identity (3.19) must also hold for these targets.

The general canonical quotient-gauge converse does not normalize
diagonal gauges for arbitrary dummy same-part F-values. Crucially,
the explicit uniform padding does set all same-part dummy F-values
to 1. We record that fact and its exact consequences for the
canonical quotient gauge and old target-part incidence.

No uniformity assumption on the original E-classes is needed.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- If all same-E dummy F-values are neutral, the chosen canonical
old gauge is also neutral toward the vertex's own E-class. -/
theorem EffectiveGeometry.canonicalGauge_samePart_one
    (D : EffectiveGeometry s V)
    (hD : ∀ x y : V, D.part x y → D.F x y = 1)
    (x : V) :
    D.toQuotientGauge.vertexGauge x (Quotient.mk D.part x) = 1 := by
  change D.F (D.representative (Quotient.mk D.part x)) x = 1
  exact hD _ _ (D.part.iseqv.symm (D.related_representative x))

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- The explicit equal-size padding has literally neutral dummy
F-values between ANY two points of the same padded E-class. -/
theorem uniformPaddedGeometry_samePart_one
    (z w : Quotient D.part × V)
    (hzw : D.uniformPaddedGeometry.part z w) :
    D.uniformPaddedGeometry.F z w = 1 := by
  classical
  have heq : D.uniformPaddedGauge.label z =
      D.uniformPaddedGauge.label w :=
    (D.uniformPaddedGeometry_part z w).mp hzw
  change D.uniformPaddedGauge.effective z w = 1
  simp [IndexedGauge.effective, heq]

/-- The canonical quotient gauge of the padded effective geometry
satisfies the manuscript's convention a_(x,[x])=1, even when the
original effective geometry had arbitrary same-part dummy F-values. -/
theorem uniformPaddedGeometry_selfGauge_one
    (z : Quotient D.part × V) :
    D.uniformPaddedGeometry.toQuotientGauge.vertexGauge z
      (Quotient.mk D.uniformPaddedGeometry.part z) = 1 := by
  exact D.uniformPaddedGeometry.canonicalGauge_samePart_one
    (D.uniformPaddedGeometry_samePart_one) z

/-- At an old embedded vertex of the padded structure, incidence
towards any OTHER blown-up part over the SAME old E-class reduces
exactly to the target valuation h(z). This is the delicate diagonal
i=j case in manuscript (3.16)--(3.19). -/
theorem uniformPaddedOldIncidence_sameIndex
    (z : Quotient D.part × V)
    (r : EffectiveWitnessPart D.uniformPaddedGeometry)
    (hr : r ≠ oldWitnessPart D.uniformPaddedGeometry z)
    (hcls : r.1 = Quotient.mk D.uniformPaddedGeometry.part z) :
    (D.uniformPaddedGeometry.oldWitnessVertex z).crossIncidence r hr =
      r.2 z := by
  change D.uniformPaddedGeometry.toQuotientGauge.vertexGauge z r.1 *
    r.2 z = r.2 z
  rw [hcls, D.uniformPaddedGeometry_selfGauge_one z]
  exact one_mul _

end EffectiveGeometry

end SemigenericEPPA
