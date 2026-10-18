import SemigenericEPPA.Algebra.RelativeResidualBaseline
import SemigenericEPPA.Structure.InvariantRawResidualMatrix
import SemigenericEPPA.Structure.RawCoverFixedGroupLift

/-!
# The fixed-cover H-lift directly from an invariant raw colouring

Suppose a finite group H acts effectively on a finite E/F rectangle
geometry. Let colour(x,y) be one H-invariant raw-colour refinement on
all cross-part ordered pairs, with correct reversal and effective
projection.

Choose a prescribed old subset S stable under H. Encode colour(x,y)
by the canonical affine-code section on each old-old pair. The
relative baseline lemma gives ONE baseline b extending these old
references exactly, and reversing affinely on every cross pair.
Encoding the full H-invariant raw colouring gives an invariant
residual matrix r which automatically agrees with b on S×S.

The previously checked finite fixed-cover homomorphic group lift
then produces a homomorphism H→Aut(raw cover) preserving literally
all E and P_c predicates, and sending each old zero-section vertex
(x,0) to (hx,0).

Thus the invariant residual matrix and its compatibility with the
chosen old baseline are NO LONGER separate hypotheses. The remaining
geometric input for the positive coherent theorem is existence of an
H-invariant raw colouring agreeing with the original old raw copy.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L] {V : Type z}
variable {d : RawDatum G C}

/-- One fixed finite raw cover carries a homomorphic H-action
extending the H-action on an H-invariant old zero-section, whenever
an H-invariant reversal-compatible raw colouring is supplied.

The baseline is chosen once and agrees with the canonical residual
section encoding of every old-old cross-part raw colour. -/
theorem exists_fixedRawCoverGroupLift_from_invariantColour
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (S : Set V)
    (hS : ∀ h : H, ∀ x, x ∈ S → rho h x ∈ S)
    (colour : V → V → C)
    (hPhi : ∀ x y, ¬D.part x y →
      d.phi (colour x y) = D.F x y)
    (hReverse : ∀ x y, ¬D.part x y →
      colour y x = d.reverse (colour x y))
    (hInvariant : ∀ (h : H) (x y : V), ¬D.part x y →
      colour (rho h x) (rho h y) = colour x y) :
    Finite (RawCoverVertex V L) ∧
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex V L)),
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        b x y = code.encodeRaw (colour x y)) ∧
      (∀ (h : H) (x : V), x ∈ S →
        lift h (x, fun _ : V => (0 : L)) =
          (rho h x, fun _ : V => (0 : L))) ∧
      (∀ (h : H) (X Y : RawCoverVertex V L),
        D.part (lift h X).1 (lift h Y).1 ↔
          D.part X.1 Y.1) ∧
      (∀ (h : H) (c : C) (X Y : RawCoverVertex V L),
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  let old : V → V → L := fun x y => code.encodeRaw (colour x y)
  have hOldReverse : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      old y x = code.shift (D.F x y) - old x y := by
    intro x y hx hy hxy
    change code.encodeRaw (colour y x) =
      code.shift (D.F x y) - code.encodeRaw (colour x y)
    calc
      code.encodeRaw (colour y x) =
        code.encodeRaw (d.reverse (colour x y)) := by
          rw [hReverse x y hxy]
      _ = code.shift (d.phi (colour x y)) -
          code.encodeRaw (colour x y) :=
            code.encodeRaw_reverse (colour x y)
      _ = code.shift (D.F x y) -
          code.encodeRaw (colour x y) := by
            rw [hPhi x y hxy]
  obtain ⟨b, hb, hbOld⟩ :=
    exists_finiteResidualBaseline_extendingSubset
      D code.shift code.shift_reverse S old hOldReverse
  obtain ⟨r, hr, hR, hRold⟩ :=
    exists_codeInvariantResidualMatrix
      D code rho colour hPhi hReverse hInvariant S b
      (by
        intro x y hx hy hxy
        exact hbOld x y hx hy hxy)
  obtain ⟨hFinite, nu, lift, hZero, hRec,
    hExt, hPart, hColour⟩ :=
    exists_fixedRawCoverGroupLift
      D code b r S hb hr hRold rho hE hF hR hS
  exact ⟨hFinite, b, hb, lift, hbOld,
    hExt, hPart, hColour⟩

end SemigenericEPPA
