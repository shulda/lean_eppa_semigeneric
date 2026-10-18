import SemigenericEPPA.Structure.RawCoverPotentialCocycle
import SemigenericEPPA.Algebra.PrescribedRawCompatibility
import SemigenericEPPA.Structure.RawCover

/-!
# Potential-based raw lifts preserve a fixed raw cover

The coherent and semi-coherent proofs fix ONE raw cover, then choose
for each finite group action a raw-colour residual matrix r_XY that
is invariant under that action. Write
    r_XY = nu_X(Y) - nu_Y(X) + b_XY.
For each base permutation theta, use the correction
    d^theta_XY = nu_(theta X)(theta Y) - nu_X(Y).

Invariance of r forces precisely equation (3.24), so the actual
raw-cover transport (3.25) preserves every original raw P_c.
Separately the cocycle lemma proves these transports compose.
Together these facts supply the algebraic part of a homomorphic
raw lift on a fixed cover, as required by Section 4 and DLF.

The construction of an invariant r satisfying old prescribed
colours and the safety condition on reversed cross-part pairs is
a distinct geometric input; this module does not assert that it
always exists.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L] {V : Type z}
variable {d : RawDatum G C}

/-- Preservation of the complete additive raw residual matrix
forces the exact antisymmetric correction equation (3.24) for
the potential difference (4.9). -/
theorem rawPotentialCorrection_compatible
    (nu b : V → V → L) (theta : Equiv.Perm V)
    (x y : V)
    (hInvariant :
      rawResidual (nu (theta x) (theta y))
        (nu (theta y) (theta x)) (b (theta x) (theta y)) =
      rawResidual (nu x y) (nu y x) (b x y)) :
    rawPotentialCorrection nu theta x y -
        rawPotentialCorrection nu theta y x =
      b x y - b (theta x) (theta y) := by
  let target : V → V → L := fun x y => nu (theta x) y
  have h := oldRawCorrectionRow_compatible
    theta b nu target x y (by simpa only [target] using hInvariant)
  change rawPotentialCorrection nu theta x y -
      rawPotentialCorrection nu theta y x =
    b x y - b (theta x) (theta y) at h
  exact h

/-- Whenever the residual labels r are theta-invariant, the
potential-based lift of theta preserves every literal raw edge
colour in the fixed residual cover. -/
theorem rawCoverPotentialLift_colour
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b nu : V → V → L)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (hInvariant : ∀ x y, ¬D.part x y →
      rawResidual (nu (theta x) (theta y))
        (nu (theta y) (theta x)) (b (theta x) (theta y)) =
      rawResidual (nu x y) (nu y x) (b x y))
    (X Y : RawCoverVertex V L) :
    rawCoverColour D code b
        (rawCoverPotentialLift nu theta X)
        (rawCoverPotentialLift nu theta Y) =
      rawCoverColour D code b X Y := by
  exact rawCoverTransport_colour D code b
    (rawPotentialCorrection nu theta) theta hE hF
    (fun x y hxy =>
      rawPotentialCorrection_compatible nu b theta x y
        (hInvariant x y hxy)) X Y

/-- The same lift is a genuine automorphism of the ACTUAL raw
rectangle-language structure: exact E and all raw relations P_c,
not only the residual matrix, are preserved and reflected. -/
theorem rawCoverPotentialLift_rawRel_iff
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b nu : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (hInvariant : ∀ x y, ¬D.part x y →
      rawResidual (nu (theta x) (theta y))
        (nu (theta y) (theta x)) (b (theta x) (theta y)) =
      rawResidual (nu x y) (nu y x) (b x y))
    (c : C) (X Y : RawCoverVertex V L) :
    rawRel (rawCoverPresentation D code b hb).toStructure c
        (rawCoverPotentialLift nu theta X)
        (rawCoverPotentialLift nu theta Y) ↔
      rawRel (rawCoverPresentation D code b hb).toStructure c X Y := by
  exact rawCoverTransport_rawRel_iff D code b hb theta hE hF
    (rawPotentialCorrection nu theta)
    (fun x y hxy =>
      rawPotentialCorrection_compatible nu b theta x y
        (hInvariant x y hxy)) c X Y

end SemigenericEPPA
