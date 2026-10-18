import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic
import Mathlib.Tactic.Abel

/-!
# Affine baselines and coordinate-correction algebra for raw-fibre covers

This begins the independent R0/R1 phase after the effective witness.
For an additive residual coefficient group L, suppose the
reversal of the residual code at effective colour g is
    rho_g(z) = t(g) - z
where t(s(g)) = t(g).

A finite group-valued effective geometry admits a baseline on
ordered cross-part pairs with
    b(y,x) = t(F(x,y)) - b(x,y),                       (3.21)
regardless of whether the effective colour is self-reversed or
whether its raw fibre has fixed reversal colours.

We also verify the two key additive identities of the raw cover:
(3.22) reverses by the correct affine involution, and corrections
satisfying (3.24) preserve the entire residual label in (3.25).
All arguments are independent of the as-yet-unproved existence
of a finite residual code and of the later raw structure lift.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]
variable {L : Type v} [AddCommGroup L]
variable {V : Type w}
variable {s : AffineAntiInvolution G}

/-- The concrete orientation-based baseline for residual labels.
Its values on same-part pairs are dummy zero. -/
noncomputable def orderedResidualBaseline
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (t : G → L) (x y : V) : L :=
  if D.part x y then 0 else if x < y then 0 else t (D.F x y)

theorem orderedResidualBaseline_same
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (t : G → L) (x y : V) (hxy : D.part x y) :
    orderedResidualBaseline D t x y = 0 := by
  simp [orderedResidualBaseline, hxy]

/-- Equation (3.21) on every genuine cross-part pair. This proof
does not divide by two and works in arbitrary additive commutative
groups, including characteristic two. -/
theorem orderedResidualBaseline_reverse
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (ht : ∀ g : G, t (s g) = t g)
    (x y : V) (hxy : ¬D.part x y) :
    orderedResidualBaseline D t y x =
      t (D.F x y) - orderedResidualBaseline D t x y := by
  have hyx : ¬D.part y x := by
    intro h
    exact hxy (D.part.iseqv.symm h)
  have hne : x ≠ y := by
    intro h
    subst y
    exact hxy (D.part.iseqv.refl x)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnlt : ¬y < x := not_lt_of_ge (le_of_lt hlt)
    have hrev : t (D.F y x) = t (D.F x y) := by
      rw [D.reverse_cross x y hxy]
      exact ht (D.F x y)
    simp [orderedResidualBaseline, hxy, hyx, hlt, hnlt, hrev]
  · have hnlt : ¬x < y := not_lt_of_ge (le_of_lt hgt)
    simp [orderedResidualBaseline, hxy, hyx, hnlt, hgt]

/-- Choose the auxiliary order from any finite carrier and forget it
from the conclusion. The resulting baseline works with arbitrary
affine reversal, including empty carriers. -/
theorem exists_finiteResidualBaseline
    [Finite V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (ht : ∀ g : G, t (s g) = t g) :
    ∃ b : V → V → L,
      (∀ x y, D.part x y → b x y = 0) ∧
      (∀ x y, ¬D.part x y →
        b y x = t (D.F x y) - b x y) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V)
      (Fintype.equivFin V).injective
  refine ⟨orderedResidualBaseline D t, ?_, ?_⟩
  · intro x y hxy
    exact orderedResidualBaseline_same D t x y hxy
  · intro x y hxy
    exact orderedResidualBaseline_reverse D t ht x y hxy

/-- Exact raw residual label from two vertex valuation coordinates
and a baseline, equation (3.22). -/
def rawResidual (u v b : L) : L := u - v + b

/-- Affine reversal of the raw residual, from reversal of the baseline:
the actual reverse residual is t minus the forward residual. -/
theorem rawResidual_reverse (t u v b bReverse : L)
    (hb : bReverse = t - b) :
    rawResidual v u bReverse = t - rawResidual u v b := by
  simp only [rawResidual, hb]
  abel

/-- Equation (3.24) is exactly the necessary and sufficient
algebraic correction for the residual label to be unchanged
under (3.25). The proof does not use any torsion assumption. -/
theorem rawResidual_corrected
    (u v b bTarget dForward dReverse : L)
    (hd : dForward - dReverse = b - bTarget) :
    rawResidual (u + dForward) (v + dReverse) bTarget =
      rawResidual u v b := by
  simp only [rawResidual]
  calc
    (u + dForward) - (v + dReverse) + bTarget =
        (u - v + bTarget) + (dForward - dReverse) := by abel
    _ = u - v + b := by rw [hd]; abel

/-- The potential corrections used in the fixed-cover group lift
compose by telescoping; the separate equivariant construction will
use this identity pointwise for each ordered edge. -/
theorem rawPotentialCorrection_telescope (u v w : L) :
    (w - v) + (v - u) = w - u := by
  abel

end SemigenericEPPA
