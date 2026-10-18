import SemigenericEPPA.Structure.RawCoverRelativePotentials
import SemigenericEPPA.Structure.RawCoverPotentialAutomorphisms

/-!
# Homomorphic raw-cover actions from one invariant residual matrix

For a finite group H acting by effective automorphisms of one fixed
base D, suppose that a residual matrix r is H-invariant and has the
correct affine reversal, and let nu be a potential representation

    r(x,y) = nu(x,y) - nu(y,x) + b(x,y).

The potential correction (4.9) gives a genuine lift of every group
element to the raw cover. The previously checked telescoping law
(4.10) makes these lifts a group homomorphism, and invariance of r
makes each lift preserve all original raw colour relations.

If nu has zero outgoing rows on a chosen H-invariant old subset S,
then these lifts carry the entire OLD ZERO-SECTION vertex
(x,0) precisely to (h x,0) for x in S. This is the prescribed-point
part of the fixed-cover homomorphic raw lift from Section 4.

The construction does not assert the existence of an H-invariant
residual matrix r; the separate orbit-colouring theorem will
provide that geometric input.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {V : Type u} {L : Type v} [AddCommGroup L]
variable {H : Type w} [Group H]
variable {G : Type t} [Group G] {C : Type t}
variable {d : RawDatum G C}

/-- A potential lift preserves the complete old zero-section
coordinate if BOTH the source and image base vertices have zero
potential rows. No invariance condition on non-old rows is needed. -/
theorem rawCoverPotentialLift_zeroSection
    (nu : V → V → L)
    (S : Set V) (hzero : ∀ x, x ∈ S → ∀ y, nu x y = 0)
    (theta : Equiv.Perm V) (x : V)
    (hx : x ∈ S) (htx : theta x ∈ S) :
    rawCoverPotentialLift nu theta
      (x, fun _ : V => (0 : L)) =
        (theta x, fun _ : V => (0 : L)) := by
  apply Prod.ext
  · rfl
  · funext y
    change (0 : L) +
      (nu (theta x) (theta (theta.symm y)) -
        nu x (theta.symm y)) = 0
    rw [theta.apply_symm_apply,
      hzero (theta x) htx y, hzero x hx (theta.symm y)]
    simp

/-- Potential corrections define a literal homomorphism of
permutation groups of the FULL residual cover, not just a
set-theoretic family of independently chosen lifts. -/
def rawCoverPotentialGroupLift
    (nu : V → V → L)
    (theta : H →* Equiv.Perm V) :
    H →* Equiv.Perm (RawCoverVertex V L) where
  toFun := fun h => rawCoverPotentialLift nu (theta h)
  map_one' := by
    change rawCoverPotentialLift nu (theta 1) =
      (1 : Equiv.Perm (RawCoverVertex V L))
    rw [map_one]
    exact rawCoverPotentialLift_id nu
  map_mul' := by
    intro h k
    change rawCoverPotentialLift nu (theta (h * k)) =
      rawCoverPotentialLift nu (theta h) *
        rawCoverPotentialLift nu (theta k)
    rw [map_mul]
    change rawCoverPotentialLift nu ((theta k).trans (theta h)) =
      (rawCoverPotentialLift nu (theta k)).trans
        (rawCoverPotentialLift nu (theta h))
    exact (rawCoverPotentialLift_trans nu (theta k) (theta h)).symm

/-- Every group element respects the prescribed old zero-section
once the old subset is invariant under its base action. -/
theorem rawCoverPotentialGroupLift_zeroSection
    (nu : V → V → L) (S : Set V)
    (hzero : ∀ x, x ∈ S → ∀ y, nu x y = 0)
    (theta : H →* Equiv.Perm V)
    (hS : ∀ h : H, ∀ x, x ∈ S → theta h x ∈ S)
    (h : H) (x : V) (hx : x ∈ S) :
    rawCoverPotentialGroupLift nu theta h
      (x, fun _ : V => (0 : L)) =
        (theta h x, fun _ : V => (0 : L)) :=
  rawCoverPotentialLift_zeroSection nu S hzero
    (theta h) x hx (hS h x hx)

/-- An invariant residual matrix ensures every element of the
potential group lift preserves each literal raw relation P_c of
the SAME fixed raw-cover presentation. -/
theorem rawCoverPotentialGroupLift_rawRel_iff
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b r nu : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (hnu : ∀ x y, ¬D.part x y →
      rawResidual (nu x y) (nu y x) (b x y) = r x y)
    (theta : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (theta h x) (theta h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (theta h x) (theta h y) = D.F x y)
    (hInvariant : ∀ h : H, ∀ x y, ¬D.part x y →
      r (theta h x) (theta h y) = r x y)
    (h : H) (c : C) (X Y : RawCoverVertex V L) :
    rawRel (rawCoverPresentation D code b hb).toStructure c
        (rawCoverPotentialGroupLift nu theta h X)
        (rawCoverPotentialGroupLift nu theta h Y) ↔
      rawRel (rawCoverPresentation D code b hb).toStructure c X Y := by
  exact rawCoverPotentialLift_rawRel_iff
    D code b nu hb (theta h) (hE h) (hF h)
    (fun x y hxy =>
      finiteRelativeRawPotentials_invariant
        D b r nu hnu (theta h) (hE h) (hInvariant h) x y hxy)
    c X Y

end SemigenericEPPA
