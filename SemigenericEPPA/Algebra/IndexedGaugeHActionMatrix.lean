import SemigenericEPPA.Structure.IndexedGauge
import Mathlib.Algebra.Group.End

/-!
# H-invariant indexed gauge matrix from genuine effective automorphisms

The nontrivial-G coherent multiplier construction uses equality
of the original noncommutative affine rank-one matrices between
old E-classes. A user of the positive EPPA theorem should not
need to supply this matrix equality as a mysterious hypothesis.

For any indexed gauge geometry P, a genuine strict H-action rho
on its vertices, a compatible part-index action iota, and
preservation of the actual effective E/F colours, the desired
matrix equality follows by unfolding the two genuine cross-colour
formulas, respecting their left-to-right noncommutative order.

This is the exact hypothesis consumed by the new anchored
occupied multiplier and cocycle theorems (#250/#251), now
derived directly from old geometric data. No finiteness or
assumptions on s(1) are required.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {V : Type w} {I : Type t}
variable {s : AffineAntiInvolution G}

/-- Literal preservation of E and effective F by a strict H-action
implies every transported old rank-one indexed gauge cross-matrix
equality, even when H permutes the old E-part labels. -/
theorem IndexedGauge.matrix_invariant_of_effective_H_action
    (P : IndexedGauge s V I)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm I)
    (hLabel : ∀ h : H, ∀ x : V,
      P.label (rho h x) = iota h (P.label x))
    (hEffective : ∀ (h : H) (x y : V),
      ¬P.toEffectiveGeometry.part x y →
      P.toEffectiveGeometry.F (rho h x) (rho h y) =
        P.toEffectiveGeometry.F x y)
    (h : H) (x y : V)
    (hxy : P.label x ≠ P.label y) :
    gaugeColour s
        (P.vertexGauge x (P.label y))
        (P.skeleton (P.label x) (P.label y))
        (P.vertexGauge y (P.label x)) =
      gaugeColour s
        (P.vertexGauge (rho h x) (iota h (P.label y)))
        (P.skeleton (iota h (P.label x))
          (iota h (P.label y)))
        (P.vertexGauge (rho h y) (iota h (P.label x))) := by
  have hCross : ¬P.toEffectiveGeometry.part x y := hxy
  have hTransported : P.label (rho h x) ≠
      P.label (rho h y) := by
    rw [hLabel h x, hLabel h y]
    exact (iota h).injective.ne hxy
  calc
    gaugeColour s
        (P.vertexGauge x (P.label y))
        (P.skeleton (P.label x) (P.label y))
        (P.vertexGauge y (P.label x)) =
      P.toEffectiveGeometry.F x y :=
        (P.effective_cross x y hxy).symm
    _ = P.toEffectiveGeometry.F (rho h x) (rho h y) :=
      (hEffective h x y hCross).symm
    _ = gaugeColour s
        (P.vertexGauge (rho h x) (P.label (rho h y)))
        (P.skeleton (P.label (rho h x))
          (P.label (rho h y)))
        (P.vertexGauge (rho h y) (P.label (rho h x))) :=
      P.effective_cross (rho h x) (rho h y) hTransported
    _ = gaugeColour s
        (P.vertexGauge (rho h x) (iota h (P.label y)))
        (P.skeleton (iota h (P.label x))
          (iota h (P.label y)))
        (P.vertexGauge (rho h y) (iota h (P.label x))) := by
      rw [hLabel h x, hLabel h y]

end SemigenericEPPA
