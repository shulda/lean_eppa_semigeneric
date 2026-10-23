import SemigenericEPPA.Bridge.GeometricNonInvariantRawCrossPairs
import SemigenericEPPA.Structure.RawCoverFixedGroupLift

/-!
# Noninvariant prescribed raw vertices on a common H-equivariant zero cover

Let H act by effective E/F automorphisms of a FINITE base D.
Prescribed raw colours on a vertex subset S need not be H-invariant.
The exact return-consistency and reversed-edge safety conditions
produce a globally H-invariant, reversal-compatible raw refinement
colour extending the original raw S-colours literally.

Encode THAT globally invariant colour as the affine residual
baseline b(x,y)=code.encodeRaw(colour x y) on ALL pairs. Because b
is H-invariant, the general fixed-cover group theorem applied with
r=b and S=univ chooses potential zero on every row, so its group
lift transports the entire zero section, not merely the old
H-invariant subset.

This is particularly useful for relative DLF: B×{1} is not
H-invariant, yet the original B old colours are retained while a
genuine strict H→Aut(rawCover) extends the selected old A action.

The relative base effective action, geometric return consistency,
and relative flip-safety still have to be discharged from the
actual phase valuation construction. No DLF conclusion is claimed.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L]
variable {V : Type z} {d : RawDatum G C}

/-- A finite raw cover carrying a strict homomorphic H-action on
its WHOLE zero section, whose induced raw structure reproduces
the prescribed colours from an arbitrary non-H-invariant old S.

All information about the old copy is preserved without assuming
that H acts on S. Only return consistency on old directed edges
is required. -/
theorem exists_nonInvariantPrescribedRawCoverGroupLift
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (S : Set V) (old : V → V → C)
    (hOldPhi : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hOldReverse : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → old y x = d.reverse (old x y))
    (hReturn : ∀ h : H, ∀ x y,
      x ∈ S → y ∈ S → ¬D.part x y →
      rho h x ∈ S → rho h y ∈ S →
      old (rho h x) (rho h y) = old x y)
    (hSafe : ∀ h : H, ∀ x y, ¬D.part x y →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    Finite (RawCoverVertex V L) ∧
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex V L)),
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        b x y = code.encodeRaw (old x y)) ∧
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        rawCoverColour D code b
          (x, fun _ : V => (0 : L))
          (y, fun _ : V => (0 : L)) = some (old x y)) ∧
      (∀ h : H, ∀ x : V,
        lift h (x, fun _ : V => (0 : L)) =
          (rho h x, fun _ : V => (0 : L))) ∧
      (∀ h : H, ∀ X Y : RawCoverVertex V L,
        D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  obtain ⟨colour, hPhi, hReverse, hInvariant, hPrescribed⟩ :=
    exists_groupInvariantRawCrossColour_extendingNonInvariantSubset
      D rho hE hF S old hOldPhi hOldReverse hReturn hSafe
  let b : V → V → L := fun x y => code.encodeRaw (colour x y)
  have hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y := by
    intro x y hxy
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
          code.encodeRaw (colour x y) := by rw [hPhi x y hxy]
  have hInvariantB : ∀ h : H, ∀ x y, ¬D.part x y →
      b (rho h x) (rho h y) = b x y := by
    intro h x y hxy
    change code.encodeRaw (colour (rho h x) (rho h y)) =
      code.encodeRaw (colour x y)
    rw [hInvariant h x y hxy]
  obtain ⟨hFinite, nu, lift, _hZeroRows, _hReconstruction,
      hAllZero, hPart, hRaw⟩ :=
    exists_fixedRawCoverGroupLift
      D code b b (Set.univ : Set V) hb hb
      (by intro x y hx hy hxy; rfl)
      rho hE hF hInvariantB
      (by intro h x hx; exact Set.mem_univ _)
  have hBaselineOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → b x y = code.encodeRaw (old x y) := by
    intro x y hx hy hxy
    change code.encodeRaw (colour x y) = code.encodeRaw (old x y)
    rw [hPrescribed x y hx hy hxy]
  refine ⟨hFinite, b, hb, lift, hBaselineOld, ?_, ?_, hPart, hRaw⟩
  · intro x y hx hy hxy
    have hProjection : d.phi (old x y) = D.F x y :=
      hOldPhi x y hx hy hxy
    have hBaseline := hBaselineOld x y hx hy hxy
    have hDecode :
        (code.decode (D.F x y)
          (code.encodeRaw (old x y))).val = old x y := by
      rw [← code.encode_of_projection (old x y)
        (D.F x y) hProjection]
      exact congrArg Subtype.val
        (code.decode_encode (D.F x y)
          ⟨old x y, hProjection⟩)
    simp only [rawCoverColour, if_neg hxy, rawResidual, zero_sub,
      sub_zero, zero_add]
    rw [hBaseline, hDecode]
  · intro h x
    exact hAllZero h x (Set.mem_univ _)

end SemigenericEPPA
