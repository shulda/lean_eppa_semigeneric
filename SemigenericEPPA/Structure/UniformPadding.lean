import SemigenericEPPA.Structure.QuotientGaugeConverse
import SemigenericEPPA.Structure.IndexedGauge
import Mathlib.Data.Fintype.Prod

/-!
# Explicit equal-size padding of an effective rectangle geometry

Before extending the old partial automorphism to a class-respecting
permutation, manuscript (3.13) first pads all E-classes to a common size.
No maximum-cardinality choice is necessary: the uniform carrier
(V/E) × V works, even when V is empty.

The embedding x ↦ ([x], x) is injective, reflects E, and preserves
every old cross-part effective colour.  The new E-classes are exactly
the first-coordinate fibres, and *each is canonically equivalent to V*.

We use the verified converse quotient-gauge theorem for the old
geometry and freely reuse its vertex gauge for every new point (i,x).
The resulting indexed gauge is a true effective rectangle geometry,
with arbitrary nonabelian G and affine reversal s.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- Old vertex embedded into the product carrier, with the true
E-class recorded as the first coordinate. -/
def paddedOldMap (x : V) : Quotient D.part × V :=
  (Quotient.mk D.part x, x)

theorem paddedOldMap_injective :
    Function.Injective D.paddedOldMap := by
  intro x y h
  exact congrArg Prod.snd h

/-- A gauge presentation on equal-sized fibres. The gauge on
(i,x) is simply the old gauge of label x; it is perfectly legitimate
when x originally belongs to a different E-class from i. -/
noncomputable def uniformPaddedGauge :
    IndexedGauge s (Quotient D.part × V) (Quotient D.part) where
  label := Prod.fst
  skeleton := D.toQuotientGauge.skeleton
  skeleton_reverse := D.toQuotientGauge.skeleton_reverse
  vertexGauge := fun z j => D.toQuotientGauge.vertexGauge z.2 j

/-- The padded structure itself, not just a set of formal labels. -/
noncomputable def uniformPaddedGeometry :
    EffectiveGeometry s (Quotient D.part × V) :=
  D.uniformPaddedGauge.toEffectiveGeometry

/-- The padded E-equivalence is exactly equality of part indices. -/
theorem uniformPaddedGeometry_part
    (z w : Quotient D.part × V) :
    D.uniformPaddedGeometry.part z w ↔ z.1 = w.1 :=
  Iff.rfl

/-- Each padded E-class has *exactly* V as its common real-label fibre.
This remains a valid equivalence for empty V and hence empty V/E. -/
def uniformPaddedFibreEquiv (i : Quotient D.part) :
    {z : Quotient D.part × V // z.1 = i} ≃ V where
  toFun := fun z => z.val.2
  invFun := fun x => ⟨(i, x), rfl⟩
  left_inv := by
    rintro ⟨⟨j, x⟩, hj⟩
    apply Subtype.ext
    exact Prod.ext hj.symm rfl
  right_inv := by
    intro x
    rfl

/-- The old E-relation is preserved and reflected under the concrete
equal-size padding. -/
theorem paddedOldMap_part (x y : V) :
    D.uniformPaddedGeometry.part (D.paddedOldMap x) (D.paddedOldMap y) ↔
      D.part x y := by
  change (Quotient.mk D.part x = Quotient.mk D.part y) ↔ D.part x y
  exact ⟨Quotient.exact, Quotient.sound⟩

/-- The padding preserves *literal* effective cross-colours, not merely
the rectangle law or an unlabelled isomorphism type. -/
theorem paddedOldMap_crossColour (x y : V)
    (hxy : ¬D.part x y) :
    D.uniformPaddedGeometry.F (D.paddedOldMap x) (D.paddedOldMap y) =
      D.F x y := by
  have hparts : Quotient.mk D.part x ≠ Quotient.mk D.part y := by
    intro h
    exact hxy (Quotient.exact h)
  have hpadded :=
    D.uniformPaddedGauge.effective_cross
      (D.paddedOldMap x) (D.paddedOldMap y) hparts
  change D.uniformPaddedGeometry.F
      (D.paddedOldMap x) (D.paddedOldMap y) =
    gaugeColour s
      (D.toQuotientGauge.vertexGauge x (Quotient.mk D.part y))
      (D.toQuotientGauge.skeleton
        (Quotient.mk D.part x) (Quotient.mk D.part y))
      (D.toQuotientGauge.vertexGauge y (Quotient.mk D.part x))
    at hpadded
  have hold := D.toQuotientGauge.effective_cross x y hxy
  change D.toQuotientGauge.toEffectiveGeometry.F x y =
    gaugeColour s
      (D.toQuotientGauge.vertexGauge x (Quotient.mk D.part y))
      (D.toQuotientGauge.skeleton
        (Quotient.mk D.part x) (Quotient.mk D.part y))
      (D.toQuotientGauge.vertexGauge y (Quotient.mk D.part x))
    at hold
  exact hpadded.trans (hold.symm.trans
    (D.quotientGauge_reconstruct_cross x y hxy))

/-- The entire padded carrier is finite if the original one is,
including in the empty-carrier case. -/
theorem finite_uniformPaddedCarrier [Finite V] :
    Finite (Quotient D.part × V) := by
  classical
  infer_instance

end EffectiveGeometry

end SemigenericEPPA
