import SemigenericEPPA.Structure.OneBaselineBothLiftModesEncoded
import SemigenericEPPA.Structure.RawCoverZeroOldEmbedding
import SemigenericEPPA.Structure.OldRawReferenceOnBase
import SemigenericEPPA.Algebra.FiniteAffineResidualCode

/-!
# One finite raw cover with a literal old zero section and both lift APIs

Fix a finite raw rectangle presentation P, a finite effective
geometry D, and ONE old effective embedding e:U↪V preserving E and
the exact effective images of original raw cross-colours.

Before choosing any later partial map or group, pick one universal
finite affine residual code, one default raw colour for irrelevant
old within-E pairs, and ONE affine baseline on V×V.

The resulting SAME raw cover has:
* the literal raw structure P as an induced old ZERO SECTION;
* individual raw automorphism extensions along every effective
  extension of an old partial raw map with invariant old reference;
* a genuine H→Perm raw cover action for every subsequently supplied
  flip-safe effective H-action with invariant old raw reference.

No arbitrary original raw reference, residual code or baseline is an
input. This is not yet the unconditional coherent EPPA theorem:
individual and safe effective actions and groupoid connectors must
still be supplied/assembled from the original structure.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {U : Type w} {V : Type z}
variable {d : RawDatum G C}

/-- A common fixed raw witness API. Its carrier is determined by the
given effective base V and the universal finite residual coefficient
group; only the raw colours of the cover vary with the selected
baseline. All fields after the baseline are simultaneously satisfied. -/
structure FixedJointRawCover
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V) where
  defaultColour : C
  code : AffineResidualCode d (UniversalResidualCarrier C)
  baseline : V → V → UniversalResidualCarrier C
  baseline_reverse : ∀ x y, ¬D.part x y →
    baseline y x = code.shift (D.F x y) - baseline x y
  old_colour : ∀ x y : U,
    rawCoverColour D code baseline
      (e x, fun _ : V => (0 : UniversalResidualCarrier C))
      (e y, fun _ : V => (0 : UniversalResidualCarrier C)) =
        P.colour x y
  individual :
    ∀ (S : Set U) (p : S → U)
        (theta : Equiv.Perm V),
      (∀ x y : S, ¬D.part (e x.val) (e y.val) →
        oldRawReferenceOnBase P e defaultColour (e (p x)) (e (p y)) =
          oldRawReferenceOnBase P e defaultColour
            (e x.val) (e y.val)) →
      (∀ x : S, theta (e x.val) = e (p x)) →
      (∀ x y, D.part (theta x) (theta y) ↔ D.part x y) →
      (∀ x y, ¬D.part x y →
        D.F (theta x) (theta y) = D.F x y) →
      ∃ T : Equiv.Perm
          (RawCoverVertex V (UniversalResidualCarrier C)),
        (∀ x : S,
          T (e x.val, fun _ : V => (0 : UniversalResidualCarrier C)) =
            (e (p x), fun _ : V => (0 : UniversalResidualCarrier C))) ∧
        (∀ X Y : RawCoverVertex V (UniversalResidualCarrier C),
          D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
        (∀ c : C,
            ∀ X Y : RawCoverVertex V (UniversalResidualCarrier C),
          rawRel
            (rawCoverPresentation D code baseline baseline_reverse).toStructure c
              (T X) (T Y) ↔
          rawRel
            (rawCoverPresentation D code baseline baseline_reverse).toStructure c
              X Y)
  safe_groups :
    ∀ (H : Type t) [Group H]
        (rho : H →* Equiv.Perm V)
        (S : Set V),
      S ⊆ Set.range e →
      (∀ h : H, ∀ x y,
        D.part (rho h x) (rho h y) ↔ D.part x y) →
      (∀ h : H, ∀ x y, ¬D.part x y →
        D.F (rho h x) (rho h y) = D.F x y) →
      (∀ h : H, ∀ x : V, x ∈ S → rho h x ∈ S) →
      (∀ h : H, ∀ x y, x ∈ S → y ∈ S →
        ¬D.part x y →
        oldRawReferenceOnBase P e defaultColour
          (rho h x) (rho h y) =
          oldRawReferenceOnBase P e defaultColour x y) →
      (∀ h : H, ∀ x y, ¬D.part x y →
        ¬(x ∈ S ∧ y ∈ S) →
        rho h x = y → rho h y = x →
        ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) →
      ∃ lift : H →* Equiv.Perm
          (RawCoverVertex V (UniversalResidualCarrier C)),
        (∀ h : H, ∀ x : V, x ∈ S →
          lift h (x, fun _ : V => (0 : UniversalResidualCarrier C)) =
            (rho h x, fun _ : V => (0 : UniversalResidualCarrier C))) ∧
        (∀ h : H,
            ∀ X Y : RawCoverVertex V (UniversalResidualCarrier C),
          D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
        (∀ h : H, ∀ c : C,
            ∀ X Y : RawCoverVertex V (UniversalResidualCarrier C),
          rawRel
            (rawCoverPresentation D code baseline baseline_reverse).toStructure c
              (lift h X) (lift h Y) ↔
          rawRel
            (rawCoverPresentation D code baseline baseline_reverse).toStructure c
              X Y)

/-- From the original literal raw presentation and an effective old
embedding, choose one concrete finite raw cover supporting both modes
of extension and reproducing ALL old raw colours on the zero section.
All auxiliary code/reference/baseline choices occur before the later
partial isomorphism or group action. -/
theorem exists_fixedJointRawCover
    [Finite G] [Finite C] [Finite V]
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V) (he : Function.Injective e)
    (hpart : ∀ x y : U, D.part (e x) (e y) ↔ P.part x y)
    (hF : ∀ x y : U, ∀ c : C,
      P.colour x y = some c → d.phi c = D.F (e x) (e y)) :
    Nonempty (FixedJointRawCover P D e) := by
  classical
  let L := UniversalResidualCarrier C
  letI : Finite L := finite_universalResidualCarrier
  let code : AffineResidualCode d L :=
    Classical.choice (exists_universalAffineResidualCode d)
  let c₀ : C := Classical.choose (d.phi_surjective 1)
  let old : V → V → C := oldRawReferenceOnBase P e c₀
  let S₀ : Set V := Set.range e
  have hPhi : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → d.phi (old x y) = D.F x y := by
    intro x y hx hy hxy
    exact oldRawReferenceOnBase_phi P D e he c₀
      hpart hF x y hx hy hxy
  have hReverse : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → old y x = d.reverse (old x y) := by
    intro x y hx hy hxy
    exact oldRawReferenceOnBase_reverse
      P D e he c₀ hpart x y hx hy hxy
  obtain ⟨b, hb, hEncoded, hIndividual, hGroups⟩ :=
    exists_oneBaseline_encodedAndBothLiftModes
      D code S₀ old hPhi hReverse e he
      (fun x => ⟨x, rfl⟩)
  have hBOld (x y : U) (hxy : ¬P.part x y) :
      b (e x) (e y) =
        code.encodeRaw (P.totalOldRawColour x y) := by
    have hc : ¬D.part (e x) (e y) := by
      intro h
      exact hxy ((hpart x y).mp h)
    calc
      b (e x) (e y) = code.encodeRaw (old (e x) (e y)) :=
        hEncoded (e x) (e y) ⟨x, rfl⟩ ⟨y, rfl⟩ hc
      _ = code.encodeRaw (P.totalOldRawColour x y) :=
        congrArg code.encodeRaw (oldRawReferenceOnBase_old
          P e he c₀ x y)
  have hOldColour (x y : U) :
      rawCoverColour D code b
        (e x, fun _ : V => (0 : L))
        (e y, fun _ : V => (0 : L)) =
          P.colour x y :=
    rawCoverZeroOldMap_colour P D code b e hpart hF hBOld x y
  exact ⟨{
    defaultColour := c₀
    code := code
    baseline := b
    baseline_reverse := hb
    old_colour := hOldColour
    individual := hIndividual
    safe_groups := hGroups
  }⟩

end SemigenericEPPA
