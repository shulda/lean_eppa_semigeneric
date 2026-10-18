import SemigenericEPPA.Algebra.ResidualBaseline

/-!
# Interpolating prescribed raw residual labels on an old embedded copy

The raw-cover embedding step is an oriented-pair valuation problem.
Suppose an old carrier U embeds injectively into an effective base V
and each ordered old cross-edge has a desired residual label ell(x,y).
If ell reverses affinely and the base baseline b satisfies (3.21),
we can choose one residual vertex valuation eta_x:V→L for each old x
such that

  eta_x(e y) - eta_y(e x) + b(e x,e y) = ell(x,y)

on every old cross edge, exactly equation (3.27).

For x<y, prescribe eta_x(e y)=ell(x,y)-b(e x,e y) and
eta_y(e x)=0. For x>y, the affine reversal equations force
the same equality automatically. Coordinates outside the old
embedding image are zero. This construction works with
noncommutative effective G and arbitrary additive coefficient L.

The labels ell will subsequently be obtained from the typed
sections of the affine residual code. This theorem is only the
exact coordinate interpolation, not yet a raw-coloured embedding.
-/

namespace SemigenericEPPA

universe u v w t

variable {G : Type u} [Group G]
variable {L : Type v} [AddCommGroup L]
variable {U : Type w} {V : Type t}
variable {s : AffineAntiInvolution G}

/-- Extend any old-indexed function to a larger carrier along an
injection, choosing zero off the image. -/
noncomputable def extendResidualAlongInjection
    (e : U → V) (he : Function.Injective e)
    (f : U → L) (y : V) : L := by
  classical
  exact if h : ∃ x : U, e x = y then f (Classical.choose h) else 0

@[simp] theorem extendResidualAlongInjection_apply
    (e : U → V) (he : Function.Injective e)
    (f : U → L) (x : U) :
    extendResidualAlongInjection e he f (e x) = f x := by
  classical
  unfold extendResidualAlongInjection
  split_ifs with h
  · have hx : Classical.choose h = x :=
      he (Classical.choose_spec h)
    rw [hx]
  · exact False.elim (h ⟨x, rfl⟩)

/-- The single oriented old-old coordinate chosen for the source x
towards target y. -/
noncomputable def orientedOldResidualCoordinate
    [LinearOrder U]
    (e : U → V) (b : V → V → L) (ell : U → U → L)
    (x y : U) : L :=
  if x < y then ell x y - b (e x) (e y) else 0

/-- Full residual valuation on V for each embedded old vertex x.
Coordinates away from the image e(U) are set to zero. -/
noncomputable def oldResidualValuation
    [LinearOrder U]
    (e : U → V) (he : Function.Injective e)
    (b : V → V → L) (ell : U → U → L)
    (x : U) : V → L :=
  extendResidualAlongInjection e he
    (orientedOldResidualCoordinate e b ell x)

@[simp] theorem oldResidualValuation_at
    [LinearOrder U]
    (e : U → V) (he : Function.Injective e)
    (b : V → V → L) (ell : U → U → L)
    (x y : U) :
    oldResidualValuation e he b ell x (e y) =
      orientedOldResidualCoordinate e b ell x y :=
  extendResidualAlongInjection_apply e he _ y

/-- The prescribed raw residual value of an old cross pair is
recovered LITERALLY from the chosen coordinate functions (3.27).
No nonemptiness, equal E-part-size or odd-order assumption. -/
theorem oldResidualValuation_recovers
    [LinearOrder U]
    (D : EffectiveGeometry s V)
    (e : U → V) (he : Function.Injective e)
    (t : G → L) (b : V → V → L) (ell : U → U → L)
    (hb : ∀ x y : V, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (hell : ∀ x y : U, ¬D.part (e x) (e y) →
      ell y x = t (D.F (e x) (e y)) - ell x y)
    (x y : U) (hxy : ¬D.part (e x) (e y)) :
    rawResidual
      (oldResidualValuation e he b ell x (e y))
      (oldResidualValuation e he b ell y (e x))
      (b (e x) (e y)) = ell x y := by
  rw [oldResidualValuation_at, oldResidualValuation_at]
  have hne : x ≠ y := by
    intro h
    subst y
    exact hxy (D.part.iseqv.refl (e x))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnlt : ¬y < x := not_lt_of_ge (le_of_lt hlt)
    simp only [orientedOldResidualCoordinate, if_pos hlt, if_neg hnlt]
    simp only [rawResidual]
    abel
  · have hnlt : ¬x < y := not_lt_of_ge (le_of_lt hgt)
    simp only [orientedOldResidualCoordinate, if_neg hnlt, if_pos hgt]
    rw [hell x y hxy, hb (e x) (e y) hxy]
    simp only [rawResidual]
    abel

end SemigenericEPPA
