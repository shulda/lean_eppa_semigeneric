import SemigenericEPPA.Algebra.RawCoverCorrections

/-!
# Completing partially prescribed raw-lift corrections (3.24), (3.28)

To lift an effective automorphism so that it sends a prescribed old
raw vertex to its specified target, the correction d(x,y) on every
outgoing edge of each selected base vertex x is already fixed:

  d(x,y) = eta_target(x)(theta y) - eta_source(x)(y).   (3.28)

We show that ANY prescribed rows R(x,y), x in S, extend to one global
correction family satisfying the affine antisymmetry law

  d(x,y)-d(y,x) = b(x,y)-b(theta x,theta y).            (3.24)

The ONLY compatibility hypothesis on prescribed data concerns pairs
with BOTH endpoints in S and distinct E-parts. There it is exactly
the same antisymmetry law for R. For mixed pairs, the reverse
correction is forced; for pairs outside S, use the already checked
orientation-based free correction. Same-E coordinates are irrelevant
to raw colours and may be prescribed independently.

This is the mathematical extension kernel for part (iv) of the raw
cover lemma, not yet a raw partial-automorphism theorem. The next
gate derives compatibility on S×S from preservation of the
section-encoded old raw colours.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]
variable {L : Type v} [AddCommGroup L]
variable {V : Type w}
variable {s : AffineAntiInvolution G}

/-- Baseline differences reverse their sign under interchange of
endpoints whenever theta preserves the effective F-colour. -/
theorem residualBaselineDifference_reverse
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (x y : V) (hxy : ¬D.part x y) :
    b y x - b (theta y) (theta x) =
      -(b x y - b (theta x) (theta y)) := by
  have htarget : ¬D.part (theta x) (theta y) := by
    intro h
    exact hxy ((hE x y).mp h)
  rw [hb x y hxy, hb (theta x) (theta y) htarget,
    hF x y hxy]
  abel

/-- A complete correction family combining prescribed rows,
algebraically forced reverse mixed rows, and free unordered pairs. -/
noncomputable def completePrescribedResidualCorrection
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (b : V → V → L)
    (theta : Equiv.Perm V)
    (S : Set V) (R : V → V → L)
    (x y : V) : L := by
  classical
  exact if D.part x y then
      (if x ∈ S then R x y else 0)
    else if x ∈ S then R x y
    else if y ∈ S then
      R y x - (b y x - b (theta y) (theta x))
    else orientedResidualCorrection D b theta x y

/-- Every prescribed row is retained LITERALLY, including coordinates
towards vertices in the same E-class (which are otherwise unused). -/
theorem completePrescribedResidualCorrection_onDomain
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (b : V → V → L)
    (theta : Equiv.Perm V)
    (S : Set V) (R : V → V → L)
    (x y : V) (hx : x ∈ S) :
    completePrescribedResidualCorrection D b theta S R x y = R x y := by
  classical
  by_cases hxy : D.part x y
  · simp [completePrescribedResidualCorrection, hxy, hx]
  · simp [completePrescribedResidualCorrection, hxy, hx]

/-- The prescribed family obeys the exact required antisymmetry
on all old cross-part pairs, no matter which endpoint is prescribed. -/
theorem completePrescribedResidualCorrection_equation
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (S : Set V) (R : V → V → L)
    (hR : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      R x y - R y x = b x y - b (theta x) (theta y))
    (x y : V) (hxy : ¬D.part x y) :
    completePrescribedResidualCorrection D b theta S R x y -
      completePrescribedResidualCorrection D b theta S R y x =
      b x y - b (theta x) (theta y) := by
  classical
  have hyx : ¬D.part y x := by
    intro h
    exact hxy (D.part.iseqv.symm h)
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · simpa [completePrescribedResidualCorrection, hxy, hyx, hx, hy]
        using hR x y hx hy hxy
    · calc
        completePrescribedResidualCorrection D b theta S R x y -
          completePrescribedResidualCorrection D b theta S R y x =
            R x y - (R x y -
              (b x y - b (theta x) (theta y))) := by
                simp [completePrescribedResidualCorrection,
                  hxy, hyx, hx, hy]
        _ = b x y - b (theta x) (theta y) := by abel
  · by_cases hy : y ∈ S
    · have hreverse :=
        residualBaselineDifference_reverse D t b hb theta hE hF x y hxy
      calc
        completePrescribedResidualCorrection D b theta S R x y -
          completePrescribedResidualCorrection D b theta S R y x =
            -(b y x - b (theta y) (theta x)) := by
              simp [completePrescribedResidualCorrection,
                hxy, hyx, hx, hy]
              abel
        _ = b x y - b (theta x) (theta y) := by
              rw [hreverse]
              abel
    · simpa [completePrescribedResidualCorrection,
        hxy, hyx, hx, hy] using
        (orientedResidualCorrection_equation D t b hb
          theta hE hF x y hxy)

/-- On a finite base every compatible prescribed collection of
old-vertex correction rows extends to one full family satisfying
(3.24), with no externally supplied linear order. -/
theorem exists_finitePrescribedResidualCorrections
    [Finite V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (S : Set V) (R : V → V → L)
    (hR : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      R x y - R y x = b x y - b (theta x) (theta y)) :
    ∃ correction : V → V → L,
      (∀ x y, x ∈ S → correction x y = R x y) ∧
      (∀ x y, ¬D.part x y →
        correction x y - correction y x =
          b x y - b (theta x) (theta y)) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V)
      (Fintype.equivFin V).injective
  let correction := completePrescribedResidualCorrection
    D b theta S R
  refine ⟨correction, ?_, ?_⟩
  · intro x y hx
    exact completePrescribedResidualCorrection_onDomain
      D b theta S R x y hx
  · intro x y hxy
    exact completePrescribedResidualCorrection_equation
      D t b hb theta hE hF S R hR x y hxy

end SemigenericEPPA
