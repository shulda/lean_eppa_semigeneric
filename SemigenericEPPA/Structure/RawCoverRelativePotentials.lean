import SemigenericEPPA.Structure.RawCoverPotentialAutomorphisms
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel

/-!
# Relative raw potentials with prescribed zero rows (manuscript 4.8)

The coherent fixed-cover construction chooses an invariant residual
matrix r whose raw colours are compatible with all prescribed old
pairs, and a baseline b on the *same fixed effective base*.

Given an old subset S such that r=b on cross-pairs from S×S, we
construct one matrix of potentials nu with the following properties:

* nu(x,y)=0 for every old x in S and every y, including same-E pairs;
* nu(x,y)-nu(y,x)+b(x,y)=r(x,y) on all cross-E pairs.

The construction orients each otherwise unconstrained unordered
cross-pair, independently of the automorphism action. Compatibility
on old-old pairs is exactly the necessary condition; affine reversal
guarantees that the equation also holds in the opposite orientation.

Together with the previously verified potential-cocycle and
potential-automorphism theorems this is the relative interpolation
kernel for the fixed-cover homomorphic raw lift. Invariance of r is
a separate hypothesis of that later theorem.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {L : Type v} [AddCommGroup L]
variable {V : Type w} {s : AffineAntiInvolution G}

/-- A potential with zero outgoing rows from S; for other unordered
cross-pairs, choose one direction to carry r-b. Values within E
are dummy zero. -/
noncomputable def relativeRawPotential
    [LinearOrder V]
    (D : EffectiveGeometry s V) (b r : V → V → L)
    (S : Set V) (x y : V) : L := by
  classical
  exact if D.part x y then 0
    else if x ∈ S then 0
    else if y ∈ S then r x y - b x y
    else if x < y then r x y - b x y else 0

/-- Every row belonging to S is literally the zero function,
not merely a row of zero differences on old cross-pairs. -/
theorem relativeRawPotential_zero
    [LinearOrder V]
    (D : EffectiveGeometry s V) (b r : V → V → L)
    (S : Set V) (x y : V) (hx : x ∈ S) :
    relativeRawPotential D b r S x y = 0 := by
  classical
  by_cases hxy : D.part x y
  · simp [relativeRawPotential, hxy]
  · simp [relativeRawPotential, hxy, hx]

/-- Reversal with the same affine shift makes the additive
difference of two residual matrices skew-symmetric. -/
theorem relativeRawDifference_reverse
    (D : EffectiveGeometry s V)
    (shift : G → L) (b r : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = shift (D.F x y) - b x y)
    (hr : ∀ x y, ¬D.part x y →
      r y x = shift (D.F x y) - r x y)
    (x y : V) (hxy : ¬D.part x y) :
    r y x - b y x = -(r x y - b x y) := by
  rw [hr x y hxy, hb x y hxy]
  abel

/-- Exact raw-residual reconstruction (4.8) on all ordered
cross-part pairs, including two old endpoints and mixed old/new
pairs, without ever modifying the chosen baseline. -/
theorem relativeRawPotential_recovers
    [LinearOrder V]
    (D : EffectiveGeometry s V)
    (shift : G → L) (b r : V → V → L) (S : Set V)
    (hb : ∀ x y, ¬D.part x y →
      b y x = shift (D.F x y) - b x y)
    (hr : ∀ x y, ¬D.part x y →
      r y x = shift (D.F x y) - r x y)
    (hOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → r x y = b x y)
    (x y : V) (hxy : ¬D.part x y) :
    rawResidual
      (relativeRawPotential D b r S x y)
      (relativeRawPotential D b r S y x)
      (b x y) = r x y := by
  classical
  have hyx : ¬D.part y x := by
    intro h
    exact hxy (D.part.iseqv.symm h)
  have hrev := relativeRawDifference_reverse D shift b r hb hr x y hxy
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · rw [relativeRawPotential_zero D b r S x y hx,
        relativeRawPotential_zero D b r S y x hy]
      simp [rawResidual, hOld x y hx hy hxy]
    · have hpot : relativeRawPotential D b r S y x =
          r y x - b y x := by
        simp [relativeRawPotential, hyx, hy, hx]
      rw [relativeRawPotential_zero D b r S x y hx, hpot,
        hrev]
      simp only [rawResidual]
      abel
  · by_cases hy : y ∈ S
    · have hpot : relativeRawPotential D b r S x y =
          r x y - b x y := by
        simp [relativeRawPotential, hxy, hx, hy]
      rw [hpot, relativeRawPotential_zero D b r S y x hy]
      simp only [rawResidual]
      abel
    · have hne : x ≠ y := by
        intro h
        subst y
        exact hxy (D.part.iseqv.refl x)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hnlt : ¬y < x := not_lt_of_ge (le_of_lt hlt)
        have hpot : relativeRawPotential D b r S x y =
            r x y - b x y := by
          simp [relativeRawPotential, hxy, hx, hy, hlt]
        have hpot' : relativeRawPotential D b r S y x = 0 := by
          simp [relativeRawPotential, hyx, hy, hx, hnlt]
        rw [hpot, hpot']
        simp only [rawResidual]
        abel
      · have hnlt : ¬x < y := not_lt_of_ge (le_of_lt hgt)
        have hpot : relativeRawPotential D b r S x y = 0 := by
          simp [relativeRawPotential, hxy, hx, hy, hnlt]
        have hpot' : relativeRawPotential D b r S y x =
            r y x - b y x := by
          simp [relativeRawPotential, hyx, hy, hx, hgt]
        rw [hpot, hpot', hrev]
        simp only [rawResidual]
        abel

/-- Finite relative-potential interpolation requires no order on the
input structure. The order is chosen internally and disappears from
the conclusion. -/
theorem exists_finiteRelativeRawPotentials
    [Finite V]
    (D : EffectiveGeometry s V)
    (shift : G → L) (b r : V → V → L) (S : Set V)
    (hb : ∀ x y, ¬D.part x y →
      b y x = shift (D.F x y) - b x y)
    (hr : ∀ x y, ¬D.part x y →
      r y x = shift (D.F x y) - r x y)
    (hOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → r x y = b x y) :
    ∃ nu : V → V → L,
      (∀ x, x ∈ S → ∀ y, nu x y = 0) ∧
      (∀ x y, ¬D.part x y →
        rawResidual (nu x y) (nu y x) (b x y) = r x y) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : LinearOrder V :=
    LinearOrder.lift' (Fintype.equivFin V)
      (Fintype.equivFin V).injective
  refine ⟨relativeRawPotential D b r S, ?_, ?_⟩
  · intro x hx y
    exact relativeRawPotential_zero D b r S x y hx
  · intro x y hxy
    exact relativeRawPotential_recovers D shift b r S
      hb hr hOld x y hxy

/-- If the target residual matrix is theta-invariant, the
interpolated potentials satisfy the exact invariant-residual
identity needed for an automorphism of the fixed raw cover. -/
theorem finiteRelativeRawPotentials_invariant
    (D : EffectiveGeometry s V)
    (b r nu : V → V → L)
    (hnu : ∀ x y, ¬D.part x y →
      rawResidual (nu x y) (nu y x) (b x y) = r x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hrInvariant : ∀ x y, ¬D.part x y →
      r (theta x) (theta y) = r x y)
    (x y : V) (hxy : ¬D.part x y) :
    rawResidual (nu (theta x) (theta y))
        (nu (theta y) (theta x)) (b (theta x) (theta y)) =
      rawResidual (nu x y) (nu y x) (b x y) := by
  have hcross : ¬D.part (theta x) (theta y) := by
    intro h
    exact hxy ((hE x y).mp h)
  calc
    rawResidual (nu (theta x) (theta y))
        (nu (theta y) (theta x)) (b (theta x) (theta y)) =
      r (theta x) (theta y) := hnu (theta x) (theta y) hcross
    _ = r x y := hrInvariant x y hxy
    _ = rawResidual (nu x y) (nu y x) (b x y) :=
      (hnu x y hxy).symm

end SemigenericEPPA
