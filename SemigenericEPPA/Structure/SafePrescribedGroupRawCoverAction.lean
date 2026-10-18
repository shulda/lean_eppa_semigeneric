import SemigenericEPPA.Bridge.GeometricPrescribedRawCrossPairs
import SemigenericEPPA.Structure.InvariantColourFixedGroupLift

/-!
# The geometric prescribed finite-group raw-cover lift

Let a group H act by effective E/F automorphisms on a finite
geometry D, and let an H-invariant old vertex subset S carry
already prescribed literal raw cross-colours.

If new endpoint-swapping H-orbits satisfy the exact self-reversing
raw-fibre safety condition, the geometric orbit theorem extends
the old colours to one global H-invariant raw refinement. The
affine-code and relative-baseline theorems turn that refinement
into ONE finite raw cover and an actual homomorphism
H → Aut(raw cover) preserving all original raw predicates.

Crucially, the old points are placed on the ZERO section and
their original raw edge colours are preserved LITERALLY, while
the H-action on these points is respected by the lifted group
homomorphism. This is a relative fixed-group action theorem.
It is NOT the unrestricted coherent groupoid extension theorem.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {L : Type t} [AddCommGroup L]
variable {V : Type z} {d : RawDatum G C}

/-- Under the precise safety condition on newly created H-orbits,
an old H-invariant raw-coloured induced subset extends on a single
finite raw cover with a homomorphic H-action. All old zero-section
colours and all old points are preserved literally.

The same raw cover, baseline, and lift homomorphism work for the
whole group H simultaneously; no group finiteness is assumed.
-/
theorem exists_safePrescribedGroupRawCoverAction
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
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
    (hSafeNew : ∀ h : H, ∀ x y,
      ¬D.part x y → ¬(x ∈ S ∧ y ∈ S) →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    Finite (RawCoverVertex V L) ∧
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex V L)),
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
  obtain ⟨hFinite, b, hb, lift, hBaseline, hExtend,
    hParts, hColours⟩ :=
    exists_fixedRawCoverGroupLift_from_invariantColour
      D code rho hE hF S hS colour hPhi hRev hInv
  refine ⟨hFinite, b, hb, lift, ?_, hExtend, hParts, hColours⟩
  intro x y hx hy hxy
  have hB : b x y = code.encodeRaw (old x y) := by
    calc
      b x y = code.encodeRaw (colour x y) :=
        hBaseline x y hx hy hxy
      _ = code.encodeRaw (old x y) :=
        congrArg code.encodeRaw (hOld x y hx hy hxy)
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
  simp [rawCoverColour, hxy, rawResidual, hB, hDecode]

end SemigenericEPPA
