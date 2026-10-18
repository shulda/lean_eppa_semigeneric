import SemigenericEPPA.Structure.EffectiveGeometry
import SemigenericEPPA.Algebra.CongruenceAction
import Mathlib.Tactic.Group

/-!
# Rectangle forcing of the congruence orbit in coherent EPPA

The negative direction of the manuscript's coherent-EPPA criterion
uses a four-vertex effective rectangle with ordered group colours

       g       s(a*g)
       a*g     d

where g is fixed by the affine reversal. The rectangle law forces

                d = a ⋆ g = a * g * s.normalized a.

These are literal equalities in the ORIGINAL effective group, even
when it is noncommutative and s(1) ≠ 1. They neither assume nor
construct coherent extensions. The companion involution argument,
to be formalized separately, shows that d has a self-reversing raw
preimage and hence that the good set S is congruence-saturated.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G]
variable {V : Type v}

/-- The exact group calculation in the orbit obstruction (4.5).
This formulation isolates the effective rectangle law from all
vertex-level or coherence assumptions. -/
theorem congruence_of_obstruction_rectangle
    (s : AffineAntiInvolution G) (a g d : G)
    (hg : s g = g)
    (hrect : g⁻¹ * s (a * g) = (a * g)⁻¹ * d) :
    d = congruence s a g := by
  have hreverse : s (a * g) = g * s.normalized a := by
    rw [s.map_mul, hg]
    simp only [AffineAntiInvolution.normalized]
    group
  have hd : d = (a * g) * (g⁻¹ * s (a * g)) := by
    calc
      d = (a * g) * ((a * g)⁻¹ * d) := by group
      _ = (a * g) * (g⁻¹ * s (a * g)) :=
        congrArg (fun x : G => (a * g) * x) hrect.symm
  rw [hd, hreverse]
  unfold congruence
  group

/-- Exactly the four-colour geometry used in the proof of the
coherent orbit obstruction: a real effective rectangle forces its
fourth colour into the congruence orbit of the first one.

No s(1)=1, abelian G, or self-reversing raw-colour hypothesis is
smuggled into the group calculation. -/
theorem EffectiveGeometry.congruence_colour_of_rectangle
    {s : AffineAntiInvolution G}
    (D : EffectiveGeometry s V)
    (u v z w : V)
    (huv : D.part u v)
    (hzw : D.part z w)
    (huz : ¬D.part u z)
    (a g : G)
    (hg : s g = g)
    (huzg : D.F u z = g)
    (hvza : D.F v z = a * g)
    (huw : D.F u w = s (a * g)) :
    D.F v w = congruence s a g := by
  have hrectangle := D.rectangle u v z w huv hzw huz
  rw [huzg, hvza, huw] at hrectangle
  exact congruence_of_obstruction_rectangle s a g (D.F v w)
    hg hrectangle

end SemigenericEPPA
