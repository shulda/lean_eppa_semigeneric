import SemigenericEPPA.Structure.RawCover
import SemigenericEPPA.Algebra.RawCoverCorrections

/-!
# Individual effective automorphisms lift to the raw-fibre cover

Fix one affine residual code and one baseline.  For an effective
automorphism theta and corrections d(x,y) satisfying manuscript
(3.24), define the literal transport of residual valuation vertices:

  (x, eta) ↦ (theta x, eta'),
  eta'(theta y) = eta(y) + d(x,y).                  (3.25)

We construct its explicit inverse and prove the transported
residual expression (3.22) is EXACTLY unchanged. It consequently
preserves and reflects every relation E and P_c in the literal raw
rectangle-language structure of RawCover. The finite correction
solver makes this lift exist for EVERY automorphism of a finite
effective geometry and for ONE FIXED baseline, independently of
the automorphism.

This does not yet assert an old raw embedding or extension of
partial raw automorphisms. Those require *prescribed corrections*
on old domain points, beyond the free correction choice below.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {V : Type z}
variable {d : RawDatum G C}

/-- Literal and invertible residual-coordinate transport (3.25).
No group action or cocycle law is assumed of the corrections. -/
def rawCoverTransport
    (theta : Equiv.Perm V) (correction : V → V → L) :
    RawCoverVertex V L ≃ RawCoverVertex V L where
  toFun := fun X =>
    (theta X.1, fun y =>
      X.2 (theta.symm y) + correction X.1 (theta.symm y))
  invFun := fun X =>
    (theta.symm X.1, fun y =>
      X.2 (theta y) - correction (theta.symm X.1) y)
  left_inv := by
    rintro ⟨x, eta⟩
    apply Prod.ext
    · exact theta.symm_apply_apply x
    · funext y
      change (eta (theta.symm (theta y)) +
        correction x (theta.symm (theta y))) -
          correction (theta.symm (theta x)) y = eta y
      simp
  right_inv := by
    rintro ⟨x, eta⟩
    apply Prod.ext
    · exact theta.apply_symm_apply x
    · funext y
      change (eta (theta (theta.symm y)) -
        correction (theta.symm x) (theta.symm y)) +
          correction (theta.symm x) (theta.symm y) = eta y
      simp

@[simp] theorem rawCoverTransport_base
    (theta : Equiv.Perm V) (correction : V → V → L)
    (X : RawCoverVertex V L) :
    (rawCoverTransport theta correction X).1 = theta X.1 := rfl

/-- The transformed residual coordinate toward theta(y) is precisely
the original coordinate toward y plus its prescribed correction. -/
theorem rawCoverTransport_coord
    (theta : Equiv.Perm V) (correction : V → V → L)
    (X : RawCoverVertex V L) (y : V) :
    (rawCoverTransport theta correction X).2 (theta y) =
      X.2 y + correction X.1 y := by
  change X.2 (theta.symm (theta y)) +
    correction X.1 (theta.symm (theta y)) =
      X.2 y + correction X.1 y
  rw [theta.symm_apply_apply]

/-- Exact preservation of the full additive residual expression
(3.22), conditional on the correction equation (3.24). -/
theorem rawCoverTransport_residual
    (b correction : V → V → L)
    (theta : Equiv.Perm V)
    (x y : V)
    (hd : correction x y - correction y x =
      b x y - b (theta x) (theta y))
    (X Y : RawCoverVertex V L)
    (hx : X.1 = x) (hy : Y.1 = y) :
    rawResidual
      ((rawCoverTransport theta correction X).2 (theta Y.1))
      ((rawCoverTransport theta correction Y).2 (theta X.1))
      (b (theta X.1) (theta Y.1)) =
        rawResidual (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1) := by
  subst x
  subst y
  rw [rawCoverTransport_coord theta correction X Y.1,
    rawCoverTransport_coord theta correction Y X.1]
  exact rawResidual_corrected (X.2 Y.1) (Y.2 X.1)
    (b X.1 Y.1) (b (theta X.1) (theta Y.1))
    (correction X.1 Y.1) (correction Y.1 X.1) hd

/-- E is preserved and reflected by every raw-cover transport
whose base permutation preserves and reflects the old E relation. -/
theorem rawCoverTransport_part_iff
    (D : EffectiveGeometry d.s V)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (correction : V → V → L)
    (X Y : RawCoverVertex V L) :
    D.part (rawCoverTransport theta correction X).1
        (rawCoverTransport theta correction Y).1 ↔
      D.part X.1 Y.1 :=
  hE X.1 Y.1

/-- An effective F-preserving base permutation and exact additive
corrections preserve each individual raw colour, not merely its
effective group image. -/
theorem rawCoverTransport_colour
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b correction : V → V → L)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (hd : ∀ x y, ¬D.part x y →
      correction x y - correction y x =
        b x y - b (theta x) (theta y))
    (X Y : RawCoverVertex V L) :
    rawCoverColour D code b
        (rawCoverTransport theta correction X)
        (rawCoverTransport theta correction Y) =
      rawCoverColour D code b X Y := by
  classical
  by_cases hxy : D.part X.1 Y.1
  · have htarget : D.part (theta X.1) (theta Y.1) :=
      (hE X.1 Y.1).2 hxy
    simp [rawCoverColour, hxy, htarget, rawCoverTransport_base]
  · have htarget : ¬D.part (theta X.1) (theta Y.1) := by
      intro h
      exact hxy ((hE X.1 Y.1).1 h)
    have hres := rawCoverTransport_residual b correction theta
      X.1 Y.1 (hd X.1 Y.1 hxy) X Y rfl rfl
    let TX := rawCoverTransport theta correction X
    let TY := rawCoverTransport theta correction Y
    have hTcross : ¬D.part TX.1 TY.1 := by
      change ¬D.part (theta X.1) (theta Y.1)
      exact htarget
    calc
      rawCoverColour D code b TX TY =
        some (code.decode (D.F TX.1 TY.1)
          (rawResidual (TX.2 TY.1) (TY.2 TX.1)
            (b TX.1 TY.1))).val := by
          simp [rawCoverColour, hTcross]
      _ = some (code.decode (D.F X.1 Y.1)
          (rawResidual (X.2 Y.1) (Y.2 X.1)
            (b X.1 Y.1))).val := by
          change some (code.decode (D.F (theta X.1) (theta Y.1))
              (rawResidual
                ((rawCoverTransport theta correction X).2 (theta Y.1))
                ((rawCoverTransport theta correction Y).2 (theta X.1))
                (b (theta X.1) (theta Y.1)))).val = _
          rw [hF X.1 Y.1 hxy, hres]
      _ = rawCoverColour D code b X Y := by
          simp [rawCoverColour, hxy]

/-- Every raw relation P_c in the ACTUAL R1–R3 structure is
preserved and reflected by the coordinate transport. -/
theorem rawCoverTransport_rawRel_iff
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (correction : V → V → L)
    (hd : ∀ x y, ¬D.part x y →
      correction x y - correction y x =
        b x y - b (theta x) (theta y))
    (c : C) (X Y : RawCoverVertex V L) :
    rawRel (rawCoverPresentation D code b hb).toStructure c
      (rawCoverTransport theta correction X)
      (rawCoverTransport theta correction Y) ↔
    rawRel (rawCoverPresentation D code b hb).toStructure c X Y := by
  change rawCoverColour D code b
    (rawCoverTransport theta correction X)
    (rawCoverTransport theta correction Y) = some c ↔
      rawCoverColour D code b X Y = some c
  rw [rawCoverTransport_colour D code b correction theta hE hF hd X Y]

/-- Every effective automorphism of a finite base has an actual
raw-colour preserving permutation lift of ONE fixed raw cover.
The lifted map preserves E and all raw P_c predicates exactly. -/
theorem exists_rawCoverAutomorphismLift
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y) :
    ∃ T : RawCoverVertex V L ≃ RawCoverVertex V L,
      (∀ X, (T X).1 = theta X.1) ∧
      (∀ X Y, D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ c : C, ∀ X Y,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (T X) (T Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  obtain ⟨correction, hd⟩ :=
    exists_finiteResidualCorrections D code.shift b hb theta hE hF
  refine ⟨rawCoverTransport theta correction, ?_, ?_, ?_⟩
  · intro X
    rfl
  · intro X Y
    exact rawCoverTransport_part_iff D theta hE correction X Y
  · intro c X Y
    exact rawCoverTransport_rawRel_iff D code b hb theta hE hF
      correction hd c X Y

end SemigenericEPPA
