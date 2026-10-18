import SemigenericEPPA.Bridge.GeometricPrescribedRawCrossPairs
import SemigenericEPPA.Structure.InvariantRawResidualMatrix
import SemigenericEPPA.Structure.RawCoverFixedGroupLift

/-!
# Relative homomorphic raw lifts with ONE PRE-CHOSEN baseline

This is the crucial quantifier order in the fixed-cover raw-lift
lemma of the manuscript: the baseline b and hence the literal raw
cover are fixed *before* choosing the subgroup H=Aut(D) of the old
partial-isomorphism groupoid.

The old subset S, its H-action and its invariant raw colours may
depend on H, but b cannot. Assume b agrees with the canonical
section codes of the prescribed old-old raw colours on S×S.
If every endpoint-swapping H-orbit outside S×S has a
self-reversing raw representative over the effective colour,
the geometric orbit-selection lemma produces an H-invariant
raw colouring agreeing with the old colours.

Encoding that colouring gives an H-invariant matrix r with the
correct affine reversal and r=b on S×S. The certified relative
potential theorem then lifts H homomorphically on the SAME fixed
raw cover. All old vertices sit at the zero section, their
raw colours are preserved, and the action is literally correct
on these vertices.

Unlike a lemma that chooses b after H, the present result can be
applied repeatedly to *different* automorphism groups of induced
substructures without changing the witness. This does not by
itself establish coherent EPPA or the DLF criterion.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L] {V : Type z}
variable {d : RawDatum G C}

/-- For one pre-chosen raw cover, a reversal-safe effective
H-action with a prescribed invariant old raw substructure has a
homomorphic raw-colour-preserving lift, with the original old
zero-section copy fixed on the nose.

The baseline b is INPUT, independent of the choice of H and S.
No H-dependent change of the underlying raw cover is made. -/
theorem exists_safePrescribedGroupLift_fixedBaseline
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (S : Set V)
    (hS : ∀ h : H, ∀ x : V, x ∈ S → rho h x ∈ S)
    (old : V → V → C)
    (hOldPhi : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hOldReverse : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → old y x = d.reverse (old x y))
    (hOldInvariant : ∀ h : H, ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      old (rho h x) (rho h y) = old x y)
    (hBOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      b x y = code.encodeRaw (old x y))
    (hSafeNew : ∀ h : H, ∀ x y,
      ¬D.part x y → ¬(x ∈ S ∧ y ∈ S) →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    Finite (RawCoverVertex V L) ∧
    ∃ lift : H →* Equiv.Perm (RawCoverVertex V L),
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        rawCoverColour D code b
          (x, fun _ : V => (0 : L))
          (y, fun _ : V => (0 : L)) = some (old x y)) ∧
      (∀ h : H, ∀ x : V, x ∈ S →
        lift h (x, fun _ : V => (0 : L)) =
          (rho h x, fun _ : V => (0 : L))) ∧
      (∀ h : H, ∀ X Y : RawCoverVertex V L,
        D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  obtain ⟨colour, hPhi, hRev, hInv, hOld⟩ :=
    exists_groupInvariantRawCrossColour_extendingSubset
      D rho hE hF S hS old
      hOldPhi hOldReverse hOldInvariant hSafeNew
  have hEncodedOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      b x y = code.encodeRaw (colour x y) := by
    intro x y hx hy hxy
    calc
      b x y = code.encodeRaw (old x y) :=
        hBOld x y hx hy hxy
      _ = code.encodeRaw (colour x y) :=
        congrArg code.encodeRaw (hOld x y hx hy hxy).symm
  obtain ⟨r, hr, hR, hrOld⟩ :=
    exists_codeInvariantResidualMatrix
      D code rho colour hPhi hRev hInv S b hEncodedOld
  obtain ⟨hFinite, nu, lift, hZero, hRec, hExt, hPart, hColour⟩ :=
    exists_fixedRawCoverGroupLift
      D code b r S hb hr hrOld rho hE hF hR hS
  refine ⟨hFinite, lift, ?_, hExt, hPart, hColour⟩
  intro x y hx hy hxy
  have hProjection : d.phi (old x y) = D.F x y :=
    hOldPhi x y hx hy hxy
  have hDecode :
      (code.decode (D.F x y)
        (code.encodeRaw (old x y))).val = old x y := by
    rw [← code.encode_of_projection (old x y)
      (D.F x y) hProjection]
    exact congrArg Subtype.val
      (code.decode_encode (D.F x y)
        ⟨old x y, hProjection⟩)
  simp [rawCoverColour, hxy, rawResidual,
    hBOld x y hx hy hxy, hDecode]

end SemigenericEPPA
