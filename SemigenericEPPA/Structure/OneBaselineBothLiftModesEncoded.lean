import SemigenericEPPA.Structure.OneBaselineBothLiftModes

/-!
# A single fixed raw baseline retaining the entire old encoded copy

This strengthened version of the common-baseline theorem explicitly
returns the encoded old-old reference equation of the chosen b.
It is necessary to certify that the SAME zero-section old embedding
is an induced raw substructure and supports both lift modes.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t q
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L]
variable {V : Type z} {U : Type q}
variable {d : RawDatum G C}

/-- One common fixed raw cover supports individual partial-map lifts
and every subsequent safe H-action, with the exact old zero-section
embedding for BOTH modes of extension. -/
theorem exists_oneBaseline_encodedAndBothLiftModes
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (S₀ : Set V)
    (old : V → V → C)
    (hPhi : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → old y x = d.reverse (old x y))
    (e : U → V) (he : Function.Injective e)
    (heS₀ : ∀ x : U, e x ∈ S₀) :
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y),
      (∀ x y, x ∈ S₀ → y ∈ S₀ → ¬D.part x y →
        b x y = code.encodeRaw (old x y)) ∧
      (∀ (S : Set U) (p : S → U)
          (theta : Equiv.Perm V),
        (∀ x y : S, ¬D.part (e x.val) (e y.val) →
          old (e (p x)) (e (p y)) =
            old (e x.val) (e y.val)) →
        (∀ x : S, theta (e x.val) = e (p x)) →
        (∀ x y, D.part (theta x) (theta y) ↔ D.part x y) →
        (∀ x y, ¬D.part x y →
          D.F (theta x) (theta y) = D.F x y) →
        ∃ T : Equiv.Perm (RawCoverVertex V L),
          (∀ x : S,
            T (e x.val, fun _ : V => (0 : L)) =
              (e (p x), fun _ : V => (0 : L))) ∧
          (∀ X Y : RawCoverVertex V L,
            D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
          (∀ c : C, ∀ X Y : RawCoverVertex V L,
            rawRel (rawCoverPresentation D code b hb).toStructure c
              (T X) (T Y) ↔
            rawRel (rawCoverPresentation D code b hb).toStructure c X Y)) ∧
      (∀ (H : Type u) [Group H]
          (rho : H →* Equiv.Perm V)
          (S : Set V),
        S ⊆ S₀ →
        (∀ h : H, ∀ x y,
          D.part (rho h x) (rho h y) ↔ D.part x y) →
        (∀ h : H, ∀ x y, ¬D.part x y →
          D.F (rho h x) (rho h y) = D.F x y) →
        (∀ h : H, ∀ x : V, x ∈ S → rho h x ∈ S) →
        (∀ h : H, ∀ x y, x ∈ S → y ∈ S →
          ¬D.part x y →
          old (rho h x) (rho h y) = old x y) →
        (∀ h : H, ∀ x y, ¬D.part x y →
          ¬(x ∈ S ∧ y ∈ S) →
          rho h x = y → rho h y = x →
          ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) →
        ∃ lift : H →* Equiv.Perm (RawCoverVertex V L),
          (∀ h : H, ∀ x : V, x ∈ S →
            lift h (x, fun _ : V => (0 : L)) =
              (rho h x, fun _ : V => (0 : L))) ∧
          (∀ h : H, ∀ X Y : RawCoverVertex V L,
            D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
          (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
            rawRel (rawCoverPresentation D code b hb).toStructure c
              (lift h X) (lift h Y) ↔
            rawRel (rawCoverPresentation D code b hb).toStructure c X Y)) := by
  classical
  obtain ⟨b, hb, hAll⟩ :=
    exists_finiteBaseline_prescribingOldRawColours
      D code S₀ old hPhi hReverse
  have hBOld (x y : U)
      (hcross : ¬D.part (e x) (e y)) :
      b (e x) (e y) = code.encodeRaw (old (e x) (e y)) :=
    hAll (Set.range e) (fun v hv => by
      obtain ⟨x, rfl⟩ := hv
      exact heS₀ x)
      (e x) (e y) ⟨x, rfl⟩ ⟨y, rfl⟩ hcross
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · intro x y hx hy hxy
    exact hAll S₀ (Subset.rfl) x y hx hy hxy
  · intro S p theta hOld hExt hE hF
    exact exists_rawCoverZeroSectionLift_alongEmbedding
      D code b hb e he (fun x y => old (e x) (e y))
        hBOld S p theta hOld hExt hE hF
  · intro H inst rho S hSS₀ hE hF hS hInv hSafe
    obtain ⟨_, lift, _hOld, hZero, hPart, hRaw⟩ :=
      exists_safePrescribedGroupLift_fixedBaseline
        D code b hb rho hE hF S hS old
        (fun x y hx hy hxy =>
          hPhi x y (hSS₀ hx) (hSS₀ hy) hxy)
        (fun x y hx hy hxy =>
          hReverse x y (hSS₀ hx) (hSS₀ hy) hxy)
        hInv (hAll S hSS₀) hSafe
    exact ⟨lift, hZero, hPart, hRaw⟩

end SemigenericEPPA
