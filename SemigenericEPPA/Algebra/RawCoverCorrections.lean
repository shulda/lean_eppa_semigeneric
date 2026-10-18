import SemigenericEPPA.Algebra.ResidualBaseline

/-!
# Pairwise corrections for automorphisms of a raw-fibre cover

Given a finite effective geometry and a reversal-compatible baseline
b of the residual additive coordinates, every automorphism theta of
the effective geometry admits corrections d(x,y) obeying
    d(x,y) - d(y,x) = b(x,y) - b(theta x, theta y).     (3.24)

The construction orients each unordered cross-part pair, choosing
its forward correction as the baseline difference and its reverse
correction as zero. The opposite orientation satisfies the equation
precisely because b reverses *affinely*, and theta preserves F.

With these corrections the residual label (3.22) is preserved by
the coordinate transport (3.25) on every ordered cross-part pair.
This is the principal additive algebra for individual raw lifts,
but is not yet a finite raw-coloured witness or a total vertex lift.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]
variable {L : Type v} [AddCommGroup L]
variable {V : Type w}
variable {s : AffineAntiInvolution G}

/-- Choose the correction in one orientation of each cross-part
unordered pair, and use zero in the opposite orientation.
Same-part values are irrelevant. -/
noncomputable def orientedResidualCorrection
    [LinearOrder V]
    (D : EffectiveGeometry s V) (b : V → V → L)
    (θ : Equiv.Perm V) (x y : V) : L :=
  if D.part x y then 0
  else if x < y then b x y - b (θ x) (θ y)
  else 0

/-- Literal equation (3.24) for EVERY cross-part ordered pair. -/
theorem orientedResidualCorrection_equation
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (θ : Equiv.Perm V)
    (hE : ∀ x y, D.part (θ x) (θ y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (θ x) (θ y) = D.F x y)
    (x y : V) (hxy : ¬D.part x y) :
    orientedResidualCorrection D b θ x y -
        orientedResidualCorrection D b θ y x =
      b x y - b (θ x) (θ y) := by
  have hyx : ¬D.part y x := by
    intro h
    exact hxy (D.part.iseqv.symm h)
  have htheta : ¬D.part (θ x) (θ y) := by
    intro h
    exact hxy ((hE x y).mp h)
  have hne : x ≠ y := by
    intro h
    subst y
    exact hxy (D.part.iseqv.refl x)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnlt : ¬y < x := not_lt_of_ge (le_of_lt hlt)
    simp [orientedResidualCorrection, hxy, hyx, hlt, hnlt]
  · have hnlt : ¬x < y := not_lt_of_ge (le_of_lt hgt)
    have hbefore := hb x y hxy
    have hafter := hb (θ x) (θ y) htheta
    calc
      orientedResidualCorrection D b θ x y -
          orientedResidualCorrection D b θ y x =
        -(b y x - b (θ y) (θ x)) := by
          simp [orientedResidualCorrection, hxy, hyx, hgt, hnlt]
      _ = b x y - b (θ x) (θ y) := by
        rw [hbefore, hafter, hF x y hxy]
        abel

/-- The explicit coordinate corrections preserve the actual raw
residual label, not merely its orbit or its effective colour. -/
theorem orientedResidualCorrection_preservesResidual
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (θ : Equiv.Perm V)
    (hE : ∀ x y, D.part (θ x) (θ y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (θ x) (θ y) = D.F x y)
    (x y : V) (hxy : ¬D.part x y)
    (u v : L) :
    rawResidual
      (u + orientedResidualCorrection D b θ x y)
      (v + orientedResidualCorrection D b θ y x)
      (b (θ x) (θ y)) =
        rawResidual u v (b x y) := by
  exact rawResidual_corrected u v (b x y) (b (θ x) (θ y))
    (orientedResidualCorrection D b θ x y)
    (orientedResidualCorrection D b θ y x)
    (orientedResidualCorrection_equation D t b hb θ hE hF x y hxy)

/-- For finite V the choice of corrections requires NO named order
on the effective structure.  The output is a complete ordered-pair
family satisfying (3.24) on all cross-part pairs. -/
theorem exists_finiteResidualCorrections
    [Finite V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (θ : Equiv.Perm V)
    (hE : ∀ x y, D.part (θ x) (θ y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (θ x) (θ y) = D.F x y) :
    ∃ d : V → V → L,
      ∀ x y, ¬D.part x y →
        d x y - d y x = b x y - b (θ x) (θ y) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V)
      (Fintype.equivFin V).injective
  refine ⟨orientedResidualCorrection D b θ, ?_⟩
  intro x y hxy
  exact orientedResidualCorrection_equation
    D t b hb θ hE hF x y hxy

end SemigenericEPPA
