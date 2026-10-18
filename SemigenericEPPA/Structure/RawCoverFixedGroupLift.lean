import SemigenericEPPA.Structure.RawCoverRelativePotentials
import SemigenericEPPA.Structure.RawCoverPotentialGroupAction
import SemigenericEPPA.Structure.RawCover

/-!
# The conditional fixed-cover homomorphic raw lift (4.8)--(4.10)

Let a group H act on one finite effective geometry D, preserving
its group-valued cross colours. Fix ONE raw residual code, ONE affine
baseline b, and ONE H-invariant additive residual matrix r with the
correct reversal. Suppose r=b on cross-pairs from an H-invariant old
subset S of D.

The relative-potential construction (4.8) produces nu with zero
outgoing rows on S and r=nu_x(y)-nu_y(x)+b_xy. The potential cocycle
(4.9)--(4.10) lifts the WHOLE H-action to a homomorphism into
automorphisms of the SAME finite raw cover, preserving every
original raw relation and taking each old zero-section vertex
(x,0) to (h x,0).

This is the algebraic conclusion of the fixed-cover finite-group
raw lift lemma; the geometric creation of H-invariant r respecting
the old raw colours and the swapped-edge safety condition is a
separate input. The theorem makes no unrestricted coherent EPPA
claim, and does not choose a different cover for different h.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H] {G : Type v} [Group G]
variable {C : Type w} {L : Type t} [AddCommGroup L]
variable {V : Type z} {d : RawDatum G C}

/-- A single finite raw cover and group homomorphism extending the
full H-action on prescribed old zero-section points, given an
H-invariant affine residual matrix on the effective base. The
finite witness is selected independently of the chosen group element. -/
theorem exists_fixedRawCoverGroupLift
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b r : V → V → L)
    (S : Set V)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (hr : ∀ x y, ¬D.part x y →
      r y x = code.shift (D.F x y) - r x y)
    (hOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → r x y = b x y)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (hR : ∀ h : H, ∀ x y, ¬D.part x y →
      r (rho h x) (rho h y) = r x y)
    (hS : ∀ h : H, ∀ x, x ∈ S → rho h x ∈ S) :
    Finite (RawCoverVertex V L) ∧
    ∃ (nu : V → V → L)
      (lift : H →* Equiv.Perm (RawCoverVertex V L)),
      (∀ x, x ∈ S → ∀ y, nu x y = 0) ∧
      (∀ x y, ¬D.part x y →
        rawResidual (nu x y) (nu y x) (b x y) = r x y) ∧
      (∀ h : H, ∀ x, x ∈ S →
        lift h (x, fun _ : V => (0 : L)) =
          (rho h x, fun _ : V => (0 : L))) ∧
      (∀ h : H, ∀ X Y : RawCoverVertex V L,
        D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  obtain ⟨nu, hZero, hRec⟩ :=
    exists_finiteRelativeRawPotentials
      D code.shift b r S hb hr hOld
  let lift : H →* Equiv.Perm (RawCoverVertex V L) :=
    rawCoverPotentialGroupLift nu rho
  refine ⟨finite_rawCoverVertices, nu, lift,
    hZero, hRec, ?_, ?_, ?_⟩
  · intro h x hx
    exact rawCoverPotentialGroupLift_zeroSection
      nu S hZero rho hS h x hx
  · intro h X Y
    change D.part
      (rawCoverTransport (rho h)
        (rawPotentialCorrection nu (rho h)) X).1
      (rawCoverTransport (rho h)
        (rawPotentialCorrection nu (rho h)) Y).1 ↔
        D.part X.1 Y.1
    exact rawCoverTransport_part_iff D (rho h) (hE h)
      (rawPotentialCorrection nu (rho h)) X Y
  · intro h c X Y
    exact rawCoverPotentialGroupLift_rawRel_iff
      D code b r nu hb hRec rho hE hF hR h c X Y

end SemigenericEPPA
