import SemigenericEPPA.Structure.NonInvariantPrescribedRawCoverGroupLift
import SemigenericEPPA.Structure.RawCoverPotentialGroupAction

/-!
# Relative raw H-action with EXPLICIT effective-base projection

The existing noninvariant-prescribed raw-cover theorem builds an
H-invariant global raw colouring of one effective base D,
encodes it as b, and lifts H through the residual cover. Its
statement exports original raw E/R_c preservation and every
zero-section action, but hides the formula for the action on the
FIRST component of an arbitrary residual vertex.

For the relative DLF safe-group induction we must know that EVERY
raw vertex of an involution-swapped pair projects to a genuinely
swapped effective-base pair. We therefore package the SAME
construction with the additional exact equation
   (lift h X).1 = rho h X.1.

The globally invariant baseline admits the ZERO potential nu=0,
so lift is the literal rawCoverPotentialGroupLift with zero
potential and inherits the equation definitionally. No new
witness outside the usual finite raw cover and no H-dependence
of the prescribed old subset or colours.

This does not assert that every involution is already complete-orbit
safe; that condition is separately supplied by the effective
group-action construction and then transferred through projection.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L]
variable {V : Type z} {d : RawDatum G C}

/-- A finite noninvariant old subset admits the SAME invariant
affine raw baseline and strict raw group lift as in the certified
construction, now with the literal global base projection of
every lifted raw vertex, not only old zero-section points. -/
theorem exists_nonInvariantPrescribedRawCoverGroupLift_withBase
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
      (∀ h : H, ∀ X : RawCoverVertex V L,
        (lift h X).1 = rho h X.1) ∧
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
  let nu : V → V → L := fun _ _ => 0
  let lift : H →* Equiv.Perm (RawCoverVertex V L) :=
    rawCoverPotentialGroupLift nu rho
  have hRec : ∀ x y, ¬D.part x y →
      rawResidual (nu x y) (nu y x) (b x y) = b x y := by
    intro x y _
    simp [nu, rawResidual]
  have hZeroRows : ∀ x, x ∈ (Set.univ : Set V) →
      ∀ y, nu x y = 0 := by
    intro x _ y
    rfl
  have hBase : ∀ h : H, ∀ X : RawCoverVertex V L,
      (lift h X).1 = rho h X.1 := by
    intro h X
    rfl
  have hAllZero : ∀ h : H, ∀ x : V,
      lift h (x, fun _ : V => (0 : L)) =
        (rho h x, fun _ : V => (0 : L)) := by
    intro h x
    exact rawCoverPotentialGroupLift_zeroSection
      nu Set.univ hZeroRows rho
      (by intro h y hy; exact Set.mem_univ _) h x (Set.mem_univ _)
  have hPart : ∀ h : H, ∀ X Y : RawCoverVertex V L,
      D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1 := by
    intro h X Y
    rw [hBase h X, hBase h Y]
    exact hE h X.1 Y.1
  have hRaw : ∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
      rawRel (rawCoverPresentation D code b hb).toStructure c
        (lift h X) (lift h Y) ↔
      rawRel (rawCoverPresentation D code b hb).toStructure c X Y := by
    intro h c X Y
    exact rawCoverPotentialGroupLift_rawRel_iff
      D code b b nu hb hRec rho hE hF hInvariantB h c X Y
  have hBaselineOld : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → b x y = code.encodeRaw (old x y) := by
    intro x y hx hy hxy
    change code.encodeRaw (colour x y) = code.encodeRaw (old x y)
    rw [hPrescribed x y hx hy hxy]
  have hOldColour : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      rawCoverColour D code b
        (x, fun _ : V => (0 : L))
        (y, fun _ : V => (0 : L)) = some (old x y) := by
    intro x y hx hy hxy
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
  exact ⟨finite_rawCoverVertices, b, hb, lift, hBaselineOld,
    hOldColour, hAllZero, hBase, hPart, hRaw⟩

end SemigenericEPPA
