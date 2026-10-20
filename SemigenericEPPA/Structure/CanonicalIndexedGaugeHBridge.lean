import SemigenericEPPA.Algebra.IndexedGaugeFixedGoodHAction
import SemigenericEPPA.Structure.QuotientGaugeConverse

/-!
# Transfer genuine old effective automorphisms to the canonical indexed gauge

The nontrivial-G group-action kernel is stated for an IndexedGauge on
an arbitrary label sort. The ordinary and coherent EPPA APIs start
from an EffectiveGeometry D, whose canonical imaginary E-sort is
Quotient D.part. We connect the two without assuming that E-classes
are nonempty by a global inhabitant (each quotient element already
has its own genuine representative).

The canonical indexed gauge has exactly D's E-relation and the same
effective cross-colours. Hence any actual H-action preserving D's E/F
data automatically supplies the hypotheses of the occupied-gauge
multiplier construction. The fixed good skeleton also agrees literally
with D's old quotient skeleton on every distinct index pair.

This is a structural bridge. Full witness H-actions and old-vertex
extension require additional separately certified steps.
-/

namespace SemigenericEPPA

universe u v w t

variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- The canonical quotient-gauge presentation, represented on an
explicit old E-index sort suitable for the H-multiplier API. -/
noncomputable def canonicalIndexedGauge (D : EffectiveGeometry d.s V) :
    IndexedGauge d.s V (Quotient D.part) :=
  IndexedGauge.ofQuotientGauge D.toQuotientGauge

/-- The indexed presentation retains the original E-relation
literally, even though the indexed Setoid is represented by a
kernel-of-label equality rather than D.part itself. -/
theorem canonicalIndexedGauge_part (D : EffectiveGeometry d.s V)
    (x y : V) :
    D.canonicalIndexedGauge.toEffectiveGeometry.part x y ↔
      D.part x y := by
  change (Quotient.mk D.part x = Quotient.mk D.part y) ↔ D.part x y
  exact ⟨Quotient.exact, Quotient.sound⟩

/-- Every true cross-part effective colour in the canonical indexed
presentation agrees with D, not merely its rectangle constraints. -/
theorem canonicalIndexedGauge_cross (D : EffectiveGeometry d.s V)
    (x y : V) (hxy : ¬D.part x y) :
    D.canonicalIndexedGauge.toEffectiveGeometry.F x y = D.F x y := by
  change (IndexedGauge.ofQuotientGauge D.toQuotientGauge).effective x y =
    D.F x y
  calc
    (IndexedGauge.ofQuotientGauge D.toQuotientGauge).effective x y =
        D.toQuotientGauge.effective x y :=
      IndexedGauge.ofQuotientGauge_effective D.toQuotientGauge x y
    _ = D.F x y := D.quotientGauge_reconstruct_cross x y hxy

/-- Every old quotient index has an actual old vertex. This does
not assert V is inhabited when it is empty; it works for each i. -/
theorem canonicalIndexedGauge_occupied (D : EffectiveGeometry d.s V)
    (i : Quotient D.part) :
    D.canonicalIndexedGauge.occupied i := by
  refine ⟨D.representative i, ?_⟩
  change Quotient.mk D.part (D.representative i) = i
  exact Quotient.out_eq i

/-- One good raw effective colour determines a skeleton which
exactly extends the old quotient skeleton on distinct indices.
It is selected solely from D and the good-colour condition,
before H, any induced subset, or any later partial arrow. -/
theorem canonicalGoodSkeleton_extendsOld
    (D : EffectiveGeometry d.s V)
    (hGood : d.selfReverseEffective.Nonempty)
    (i j : Quotient D.part) (hij : i ≠ j) :
    D.canonicalIndexedGauge.fixedGoodSkeleton hGood i j =
      D.toQuotientGauge.skeleton i j := by
  have hi : D.canonicalIndexedGauge.occupied i :=
    D.canonicalIndexedGauge_occupied i
  have hj : D.canonicalIndexedGauge.occupied j :=
    D.canonicalIndexedGauge_occupied j
  exact D.canonicalIndexedGauge.fixedGoodSkeleton_old
    hGood i j hi hj hij

/-- Genuine H-preservation of D's E/F data implies preservation
of the canonical indexed presentation, with NO additional gauge
matrix-invariance assumption and no demand on same-part dummies. -/
theorem canonicalIndexedGauge_H_invariant
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ (h : H) (x y : V),
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ (h : H) (x y : V), ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y) :
    ∀ (h : H) (x y : V),
      ¬D.canonicalIndexedGauge.toEffectiveGeometry.part x y →
      D.canonicalIndexedGauge.toEffectiveGeometry.F
        (rho h x) (rho h y) =
        D.canonicalIndexedGauge.toEffectiveGeometry.F x y := by
  intro h x y hCross
  have hxy : ¬D.part x y := by
    intro hpart
    exact hCross ((D.canonicalIndexedGauge_part x y).2 hpart)
  have hxy' : ¬D.part (rho h x) (rho h y) := by
    intro hpart
    exact hxy ((hE h x y).1 hpart)
  calc
    D.canonicalIndexedGauge.toEffectiveGeometry.F
        (rho h x) (rho h y) = D.F (rho h x) (rho h y) :=
      D.canonicalIndexedGauge_cross (rho h x) (rho h y) hxy'
    _ = D.F x y := hF h x y hxy
    _ = D.canonicalIndexedGauge.toEffectiveGeometry.F x y :=
      (D.canonicalIndexedGauge_cross x y hxy).symm

/-- Quotient-class compatibility of an old H-action is exactly
compatibility of its canonical IndexedGauge old-vertex labels.
There is no independently chosen second-part identification. -/
theorem canonicalIndexedGauge_H_labels
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x)) :
    ∀ (h : H) (x : V),
      D.canonicalIndexedGauge.label (rho h x) =
        iota h (D.canonicalIndexedGauge.label x) := by
  intro h x
  exact hcls h x

end EffectiveGeometry

end SemigenericEPPA
