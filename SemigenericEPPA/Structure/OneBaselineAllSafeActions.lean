import SemigenericEPPA.Algebra.FixedOldRawBaseline
import SemigenericEPPA.Structure.SafePrescribedGroupLiftFixedBaseline

/-!
# One fixed raw cover for all subsequent safe group actions

The coherent-EPPA fixed-cover lemma must choose the raw witness
BEFORE choosing an induced old substructure or its automorphism
group.  Construct the affine baseline once using the raw colours
of a whole old subset S₀.  Then quantify over *all* groups H,
their effective E/F-actions, and all H-invariant S ⊆ S₀.

Provided the prescribed old colours are H-invariant and all
endpoint-swapping new cross-pair orbits are reversal-safe, the
same baseline supports a genuine group homomorphism of H into
automorphisms of the SAME raw-coloured cover.  Every old zero
section and each literal raw P_c relation is preserved.

This closes the quantifier-order step in the manuscript's
fixed-cover finite-group raw lift, conditional only on the
safety of the chosen effective group action.  It does not claim
the existence of those safe actions or coherent groupoid EPPA.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type v} [Group G]
variable {C : Type w} {L : Type z} [AddCommGroup L]
variable {V : Type u} {d : RawDatum G C}

/-- Fix ONE finite raw witness baseline independent of all later
groups and induced subsets. For every reversal-safe effective
group action H that extends the prescribed old raw colours on
S ⊆ S₀, there is a homomorphic raw-cover lift on the very same
carrier, preserving E, all P_c, and the old zero-section points. -/
theorem exists_oneBaseline_allSafePrescribedGroupLifts
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (S₀ : Set V)
    (old : V → V → C)
    (hPhi : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → old y x = d.reverse (old x y)) :
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y),
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
          (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
            rawCoverColour D code b
              (x, fun _ : V => (0 : L))
              (y, fun _ : V => (0 : L)) =
              some (old x y)) ∧
          (∀ h : H, ∀ x : V, x ∈ S →
            lift h (x, fun _ : V => (0 : L)) =
              (rho h x, fun _ : V => (0 : L))) ∧
          (∀ h : H, ∀ X Y : RawCoverVertex V L,
            D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
          (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
            rawRel
              (rawCoverPresentation D code b hb).toStructure c
                (lift h X) (lift h Y) ↔
            rawRel
              (rawCoverPresentation D code b hb).toStructure c X Y)) := by
  classical
  obtain ⟨b, hb, hAll⟩ :=
    exists_finiteBaseline_prescribingOldRawColours
      D code S₀ old hPhi hReverse
  refine ⟨b, hb, ?_⟩
  intro H inst rho S hSS₀ hE hF hS hInv hSafe
  obtain ⟨_, lift, hOld, hZero, hPart, hRaw⟩ :=
    exists_safePrescribedGroupLift_fixedBaseline
      D code b hb rho hE hF S hS old
      (fun x y hx hy hxy =>
        hPhi x y (hSS₀ hx) (hSS₀ hy) hxy)
      (fun x y hx hy hxy =>
        hReverse x y (hSS₀ hx) (hSS₀ hy) hxy)
      hInv
      (hAll S hSS₀)
      hSafe
  exact ⟨lift, hOld, hZero, hPart, hRaw⟩

end SemigenericEPPA
