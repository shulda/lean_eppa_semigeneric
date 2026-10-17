import SemigenericEPPA.Structure.QuotientGauge
import SemigenericEPPA.Algebra.Rectangle
import Mathlib.Tactic.Group

/-!
# Reconstruction of quotient-gauge coordinates from effective geometry

This is the converse of manuscript's two-sorted gauge presentation
(2.6): every group-valued E-rectangle geometry admits a system of
K_ij and λ_(x,j) on its canonical quotient imaginary sort V/E.

We use Quotient.out to choose one old anchor in each E-class.
The skeleton is K_ij = F(out(i),out(j)), and the gauge coordinate
λ_(x,j) is the reverse edge F(out(j),x).

The produced gauge geometry has exactly the same effective F on
ALL cross-part ordered pairs, including the nonabelian and
nontrivially affine cases. Same-part dummy values are immaterial.
No nonempty/finite carrier assumption is needed.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- Chosen representative of a canonical part-imaginary vertex. -/
noncomputable def representative (i : Quotient D.part) : V :=
  Quotient.out i

/-- Every real vertex belongs to the E-part of its chosen quotient
representative. -/
theorem related_representative (x : V) :
    D.part x (D.representative (Quotient.mk D.part x)) := by
  apply Quotient.exact
  exact (Quotient.out_eq (Quotient.mk D.part x)).symm

/-- The usual noncommutative factorization is a direct consequence
of one rectangle; this version is independent of chosen subtypes. -/
theorem anchored_factor
    (x p q y : V)
    (hxp : D.part x p)
    (hqy : D.part q y)
    (hxq : ¬D.part x q) :
    D.F x y = D.F x q * (D.F p q)⁻¹ * D.F p y := by
  have hr := D.rectangle x p q y hxp hqy hxq
  calc
    D.F x y = D.F x q * ((D.F x q)⁻¹ * D.F x y) := by group
    _ = D.F x q * ((D.F p q)⁻¹ * D.F p y) := by rw [hr]
    _ = D.F x q * (D.F p q)⁻¹ * D.F p y := by group

/-- The actual effective geometry canonically admits a gauge
presentation after choosing one representative per quotient class. -/
noncomputable def toQuotientGauge : QuotientGauge s V where
  part := D.part
  skeleton := fun i j => D.F (D.representative i) (D.representative j)
  skeleton_reverse := by
    intro i j hij
    have hcross :
        ¬D.part (D.representative i) (D.representative j) := by
      intro h
      apply hij
      calc
        i = Quotient.mk D.part (D.representative i) :=
          (Quotient.out_eq i).symm
        _ = Quotient.mk D.part (D.representative j) :=
          Quotient.sound h
        _ = j := Quotient.out_eq j
    exact D.reverse_cross (D.representative i)
      (D.representative j) hcross
  vertexGauge := fun x j => D.F (D.representative j) x

/-- Reconstructing via quotient gauges returns the original
group-valued colour on each cross-part ordered pair. -/
theorem quotientGauge_reconstruct_cross
    (x y : V) (hxy : ¬D.part x y) :
    D.toQuotientGauge.toEffectiveGeometry.F x y = D.F x y := by
  let p : V := D.representative (Quotient.mk D.part x)
  let q : V := D.representative (Quotient.mk D.part y)
  have hxp : D.part x p := D.related_representative x
  have hqy : D.part q y :=
    D.part.iseqv.symm (D.related_representative y)
  have hxq : ¬D.part x q := by
    intro h
    exact hxy (D.part.iseqv.trans h hqy)
  have hfact := D.anchored_factor x p q y hxp hqy hxq
  have hreverse : s (D.F q x) = D.F x q := by
    rw [D.reverse_cross x q hxq, s.involutive]
  have hformula :
      D.toQuotientGauge.toEffectiveGeometry.F x y =
        gaugeColour s (D.F q x) (D.F p q) (D.F p y) := by
    have h := D.toQuotientGauge.effective_cross x y hxy
    change D.toQuotientGauge.toEffectiveGeometry.F x y =
      gaugeColour s (D.F q x) (D.F p q) (D.F p y) at h
    exact h
  calc
    D.toQuotientGauge.toEffectiveGeometry.F x y =
      gaugeColour s (D.F q x) (D.F p q) (D.F p y) := hformula
    _ = D.F x q * (D.F p q)⁻¹ * D.F p y := by
      simp only [gaugeColour, hreverse]
    _ = D.F x y := hfact.symm

/-- The canonical gauge round trip preserves E literally. -/
theorem quotientGauge_reconstruct_part (x y : V) :
    D.toQuotientGauge.toEffectiveGeometry.part x y ↔ D.part x y :=
  Iff.rfl

end EffectiveGeometry
end SemigenericEPPA
