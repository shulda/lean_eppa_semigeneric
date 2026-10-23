import SemigenericEPPA.Structure.NonInvariantPrescribedRawCoverGroupLift
import SemigenericEPPA.Structure.RawCoverZeroSectionIndividualLifts
import SemigenericEPPA.Structure.TotalOldRawPalette

/-!
# Relative SAFE finite raw witness: H-actions and partial map connectors

Given an old finite R1--R3 raw structure P embedded into ONE
finite effective geometry D, suppose:
* H acts on D by actual E/F automorphisms, with the original
  old P raw-colour reference preserving its values under returns
  of H-translates to the (NOT H-invariant) old image;
* every reversed cross-E edge for the actual H-action admits
  a raw self-reversing colour;
* every partial raw isomorphism of P admits an INDIVIDUAL full
  effective D-automorphism extending that very fixed old embedding.

Then the noninvariant raw orbit construction creates a global
H-invariant raw refinement. Choose its canonical affine baseline
once, before specifying a partial map. The same finite raw-cover
zero section literally embeds P and carries a strict H-group
action preserving ALL original E and R_c predicates.

Finally the independently certified zero-section raw lift extends
EVERY partial raw P-isomorphism along that SAME old embedding
and the SAME affine baseline. No second witness or H-dependent
reset of its residual encoding is allowed.

This is the RAW joint-extension conclusion required for relative
safe EPPA. The effective base D, safe action and its individual
old partial extensions are inputs; constructing these simultaneously
for arbitrary A⊆B with only H≤Aut(A) remains another proof gate.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z q
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L]
variable {U : Type q} {V : Type z}
variable {d : RawDatum G C}

/-- One finite raw witness simultaneously extends a prescribed
safe H-action and every individual raw partial isomorphism.

The old P embedding is the LITERAL zero-section of a single
raw cover, whose baseline is chosen only once. H need not act on
P. Repeated old points are not copied into distinct raw witnesses. -/
theorem RawRectanglePresentation.exists_relativeSafeRawJointWitness_of_effectiveData
    [Finite V] [Finite L]
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V) (he : Function.Injective e)
    (hPartEmbed : ∀ x y : U,
      D.part (e x) (e y) ↔ P.part x y)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (old : V → V → C)
    (hOldExact : ∀ x y : U,
      old (e x) (e y) = P.totalOldRawColour x y)
    (hOldPhi : ∀ x y, x ∈ Set.range e → y ∈ Set.range e →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hOldReverse : ∀ x y, x ∈ Set.range e → y ∈ Set.range e →
      ¬D.part x y → old y x = d.reverse (old x y))
    (hReturn : ∀ h : H, ∀ x y,
      x ∈ Set.range e → y ∈ Set.range e →
      ¬D.part x y →
      rho h x ∈ Set.range e → rho h y ∈ Set.range e →
      old (rho h x) (rho h y) = old x y)
    (hSafe : ∀ h : H, ∀ x y, ¬D.part x y →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c)
    (hEffectivePartial : ∀ (T : Set U) (p : T → U),
      Function.Injective p →
      (∀ x y : T, P.part x.val y.val ↔ P.part (p x) (p y)) →
      (∀ x y : T, P.colour (p x) (p y) = P.colour x.val y.val) →
      ∃ theta : Equiv.Perm V,
        (∀ x : T, theta (e x.val) = e (p x)) ∧
        (∀ x y, D.part (theta x) (theta y) ↔ D.part x y) ∧
        (∀ x y, ¬D.part x y →
          D.F (theta x) (theta y) = D.F x y)) :
    Finite (RawCoverVertex V L) ∧
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex V L)),
      (∀ x y : U,
        rawCoverColour D code b
          (e x, fun _ : V => (0 : L))
          (e y, fun _ : V => (0 : L)) = P.colour x y) ∧
      (∀ h : H, ∀ x : V,
        lift h (x, fun _ : V => (0 : L)) =
          (rho h x, fun _ : V => (0 : L))) ∧
      (∀ h : H, ∀ X Y : RawCoverVertex V L,
        D.part (lift h X).1 (lift h Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) ∧
      (∀ (T : Set U) (p : T → U),
        Function.Injective p →
        (∀ x y : T, P.part x.val y.val ↔ P.part (p x) (p y)) →
        (∀ x y : T, P.colour (p x) (p y) = P.colour x.val y.val) →
        ∃ beta : Equiv.Perm (RawCoverVertex V L),
          (∀ x : T,
            beta (e x.val, fun _ : V => (0 : L)) =
              (e (p x), fun _ : V => (0 : L))) ∧
          (∀ X Y : RawCoverVertex V L,
            D.part (beta X).1 (beta Y).1 ↔ D.part X.1 Y.1) ∧
          (∀ c : C, ∀ X Y : RawCoverVertex V L,
            rawRel (rawCoverPresentation D code b hb).toStructure c
              (beta X) (beta Y) ↔
            rawRel (rawCoverPresentation D code b hb).toStructure c
              X Y)) := by
  classical
  let S : Set V := Set.range e
  obtain ⟨hFinite, b, hb, lift, hbOld, hColourS,
      hAllZero, hPart, hRaw⟩ :=
    exists_nonInvariantPrescribedRawCoverGroupLift
      D code rho hE hF S old
      hOldPhi hOldReverse hReturn hSafe
  have hbOldP : ∀ x y : U, ¬D.part (e x) (e y) →
      b (e x) (e y) =
        code.encodeRaw (P.totalOldRawColour x y) := by
    intro x y hxy
    calc
      b (e x) (e y) = code.encodeRaw (old (e x) (e y)) :=
        hbOld (e x) (e y) ⟨x,rfl⟩ ⟨y,rfl⟩ hxy
      _ = code.encodeRaw (P.totalOldRawColour x y) :=
        congrArg code.encodeRaw (hOldExact x y)
  have hOldColour (x y : U) :
      rawCoverColour D code b
        (e x, fun _ : V => (0 : L))
        (e y, fun _ : V => (0 : L)) = P.colour x y := by
    by_cases hxy : P.part x y
    · have hpart : D.part (e x) (e y) := (hPartEmbed x y).mpr hxy
      exact ((rawCoverColour_none_iff D code b _ _).mpr hpart).trans
        ((P.colour_none_iff x y).mpr hxy).symm
    · have hexy : ¬D.part (e x) (e y) := by
        intro heq
        exact hxy ((hPartEmbed x y).mp heq)
      calc
        rawCoverColour D code b
            (e x, fun _ : V => (0 : L))
            (e y, fun _ : V => (0 : L)) =
          some (old (e x) (e y)) :=
            hColourS (e x) (e y) ⟨x,rfl⟩ ⟨y,rfl⟩ hexy
        _ = some (P.totalOldRawColour x y) := by rw [hOldExact x y]
        _ = P.colour x y :=
          (P.totalOldRawColour_cross x y hxy).symm
  refine ⟨hFinite, b, hb, lift, hOldColour,
    hAllZero, hPart, hRaw, ?_⟩
  intro T p hp hOldPart hOldColour
  obtain ⟨theta, hthetaOld, hthetaE, hthetaF⟩ :=
    hEffectivePartial T p hp hOldPart hOldColour
  have hOldCross (x y : T)
      (hxy : ¬D.part (e x.val) (e y.val)) :
      P.totalOldRawColour (p x) (p y) =
        P.totalOldRawColour x.val y.val := by
    have hxyP : ¬P.part x.val y.val := by
      intro hh
      exact hxy ((hPartEmbed x.val y.val).mpr hh)
    have hnewP : ¬P.part (p x) (p y) := by
      intro hh
      exact hxyP ((hOldPart x y).mpr hh)
    apply Option.some.inj
    calc
      some (P.totalOldRawColour (p x) (p y)) =
          P.colour (p x) (p y) :=
        (P.totalOldRawColour_cross (p x) (p y) hnewP).symm
      _ = P.colour x.val y.val := hOldColour x y
      _ = some (P.totalOldRawColour x.val y.val) :=
        P.totalOldRawColour_cross x.val y.val hxyP
  exact exists_rawCoverZeroSectionLift_alongEmbedding
    D code b hb e he P.totalOldRawColour hbOldP
    T p theta hOldCross hthetaOld hthetaE hthetaF

end SemigenericEPPA
