import SemigenericEPPA.Structure.DLFRelativeSafeRawJointWithBase
import SemigenericEPPA.Structure.DLFPhaseSafeRawJointFromEffective
import SemigenericEPPA.Valuations.DLFPhaseIndividualEffectiveExtension
import SemigenericEPPA.Structure.OldRawReferenceGroupInvariance
import SemigenericEPPA.Valuations.EmbeddedOldSubsetEquivariance
import SemigenericEPPA.Valuations.DLFRelativeRawOldPhaseSafety
import SemigenericEPPA.Valuations.DLFPhaseOldReturnConsistency
import Mathlib.Data.Fintype.Prod

/-!
# Relative safe raw EPPA: automatic regular phase and one raw joint cover

Given an ACTUAL finite effective E/F witness D of an original
finite raw B, a strict H-action rho extending a genuine selected
raw automorphism action on A⊆B, and individual effective
automorphisms of every partial raw B-map, assume the genuine
relative DLF involution condition on rho's swapped cross-pairs:
their colours have complete good affine congruence orbits.

ALL raw phase hypotheses are then automatic. The selected old A
zero-copy is invariant but the larger B zero-copy is NOT H-invariant.
Take a regular H phase over every vertex outside A, fix phases
over A, and use the literal raw B-reference through the embedding
e. The certified return-consistency lemma proves that any
H-translate of two phase-one B points returning to that phase
preserves the actual old raw colours. No fictitious group action
on the remainder B\A is assumed.

The certified raw joint-lift constructs ONE finite residual cover
and strict H-group action preserving all original binary E/R_c
predicates, while on the SAME old phase-one zero section EVERY
individual raw partial isomorphism of B extends. The required
individual effective automorphisms remain independent of the
prescribed H action and survive the phase expansion unchanged.

The theorem does not construct D/rho from a safe old H-action:
the fixed-factorial relative effective witness is a separate gate.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {G : Type u} [Group G] {C : Type v}
variable {U : Type w} {V : Type t} [Finite V]
variable {H : Type z} [Group H] [Finite H]
variable {L : Type u} [AddCommGroup L] [Finite L]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Given one finite effective base with genuine selected safe H
group action and all individual old effective connectors, its
regular-phase expansion admits ONE finite original raw witness
supporting BOTH lift modes on the SAME literal old zero section.

Only the selected old raw action needs to be H-invariant. -/
theorem exists_relativePhaseRawJointWitness_of_effectiveAction_withBase
    (Praw : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V) (he : Function.Injective e)
    (hPartEmbed : ∀ x y : U,
      D.part (e x) (e y) ↔ Praw.part x y)
    (hColourEmbed : ∀ x y : U, ∀ c : C,
      Praw.colour x y = some c →
        d.phi c = D.F (e x) (e y))
    (S : Set U) (rhoS : H →* Equiv.Perm S)
    (hPartOld : ∀ (h : H) (x y : S),
      Praw.part (rhoS h x).val (rhoS h y).val ↔
        Praw.part x.val y.val)
    (hColourOld : ∀ (h : H) (x y : S),
      Praw.colour (rhoS h x).val (rhoS h y).val =
        Praw.colour x.val y.val)
    (rho : H →* Equiv.Perm V)
    (hOldExt : ∀ (h : H) (x : S),
      rho h (e x.val) = e (rhoS h x).val)
    (hE : ∀ (h : H) (x y : V),
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ (h : H) (x y : V), ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (hSafeInvol : ∀ (h : H) (x y : V),
      h * h = 1 → ¬D.part x y →
      rho h x = y → rho h y = x →
      d.GoodCompleteOrbitAt (D.F x y))
    (hPartial : ∀ (T : Set U) (p : T → U),
      Function.Injective p →
      (∀ x y : T, Praw.part x.val y.val ↔
        Praw.part (p x) (p y)) →
      (∀ x y : T,
        Praw.colour (p x) (p y) = Praw.colour x.val y.val) →
      ∃ theta : Equiv.Perm V,
        (∀ x : T, theta (e x.val) = e (p x)) ∧
        (∀ x y : V, D.part (theta x) (theta y) ↔
          D.part x y) ∧
        (∀ x y : V, ¬D.part x y →
          D.F (theta x) (theta y) = D.F x y)) :
    let ePhase : U → V × H := fun x => (e x, 1)
    let DPhase := D.phasePullback H
    Finite (RawCoverVertex (V × H) L) ∧
    ∃ (b : (V × H) → (V × H) → L)
      (hb : ∀ x y, ¬DPhase.part x y →
        b y x = code.shift (DPhase.F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex (V × H) L)),
      (∀ x y : U,
        rawCoverColour DPhase code b
          (ePhase x, fun _ : V × H => (0 : L))
          (ePhase y, fun _ : V × H => (0 : L)) =
            Praw.colour x y) ∧
      (∀ h : H, ∀ x : V × H,
        lift h (x, fun _ : V × H => (0 : L)) =
          (relativePhaseAction rho
              (embeddedOldSubset e S)
              (embeddedOldSubset_invariant e S rhoS rho hOldExt)
              h x, fun _ : V × H => (0 : L))) ∧
      (∀ h : H, ∀ X : RawCoverVertex (V × H) L,
        (lift h X).1 =
          relativePhaseAction rho (embeddedOldSubset e S)
            (embeddedOldSubset_invariant e S rhoS rho hOldExt)
            h X.1) ∧
      (∀ h : H, ∀ X Y : RawCoverVertex (V × H) L,
        DPhase.part (lift h X).1 (lift h Y).1 ↔
          DPhase.part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex (V × H) L,
        rawRel (rawCoverPresentation DPhase code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation DPhase code b hb).toStructure c
          X Y) ∧
      (∀ (T : Set U) (p : T → U),
        Function.Injective p →
        (∀ x y : T, Praw.part x.val y.val ↔
          Praw.part (p x) (p y)) →
        (∀ x y : T,
          Praw.colour (p x) (p y) = Praw.colour x.val y.val) →
        ∃ beta : Equiv.Perm (RawCoverVertex (V × H) L),
          (∀ x : T,
            beta (ePhase x.val, fun _ : V × H => (0 : L)) =
              (ePhase (p x), fun _ : V × H => (0 : L))) ∧
          (∀ X Y : RawCoverVertex (V × H) L,
            DPhase.part (beta X).1 (beta Y).1 ↔
              DPhase.part X.1 Y.1) ∧
          (∀ c : C, ∀ X Y : RawCoverVertex (V × H) L,
            rawRel (rawCoverPresentation DPhase code b hb).toStructure c
              (beta X) (beta Y) ↔
            rawRel (rawCoverPresentation DPhase code b hb).toStructure c
              X Y)) := by
  classical
  let Aimg : Set V := embeddedOldSubset e S
  let Bimg : Set V := Set.range e
  let ePhase : U → V × H := fun x => (e x, 1)
  let DPhase := D.phasePullback H
  let rhoPhase : H →* Equiv.Perm (V × H) :=
    relativePhaseAction rho Aimg
      (embeddedOldSubset_invariant e S rhoS rho hOldExt)
  let oldRaw : V → V → C :=
    oldRawReferenceOnBase Praw e
      (Classical.choose (d.phi_surjective 1))
  let oldPhase : (V × H) → (V × H) → C :=
    fun x y => oldRaw x.1 y.1
  have hA : ∀ (h : H) (x : V),
      x ∈ Aimg ↔ rho h x ∈ Aimg :=
    embeddedOldSubset_invariant e S rhoS rho hOldExt
  have hAinB : Aimg ⊆ Bimg := by
    rintro x ⟨a, rfl⟩
    exact ⟨a.val, rfl⟩
  have hRawBPhi : ∀ x y : V, x ∈ Bimg → y ∈ Bimg →
      ¬D.part x y → d.phi (oldRaw x y) = D.F x y := by
    intro x y hx hy hxy
    exact oldRawReferenceOnBase_phi Praw D e he
      (Classical.choose (d.phi_surjective 1))
      hPartEmbed hColourEmbed x y hx hy hxy
  have hRawBReverse : ∀ x y : V, x ∈ Bimg → y ∈ Bimg →
      ¬D.part x y → oldRaw y x = d.reverse (oldRaw x y) := by
    intro x y hx hy hxy
    exact oldRawReferenceOnBase_reverse Praw D e he
      (Classical.choose (d.phi_surjective 1))
      hPartEmbed x y hx hy hxy
  have hRawAInvariant : ∀ (h : H) (x y : V),
      x ∈ Aimg → y ∈ Aimg → ¬D.part x y →
      oldRaw (rho h x) (rho h y) = oldRaw x y := by
    intro h x y hx hy hcross
    exact oldRawReferenceOnBase_groupInvariant
      Praw D e he (Classical.choose (d.phi_surjective 1))
      hPartEmbed S rhoS
      (fun h a b => (hPartOld h a b).symm)
      hColourOld rho hOldExt h x y hx hy hcross
  have hRawAInvariantAll : ∀ (h : H) (x y : V),
      x ∈ Aimg → y ∈ Aimg →
      oldRaw (rho h x) (rho h y) = oldRaw x y := by
    intro h x y hx hy
    by_cases hxy : D.part x y
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      have hab : Praw.part a.val b.val :=
        (hPartEmbed a.val b.val).mp hxy
      have habNew :
          Praw.part (rhoS h a).val (rhoS h b).val :=
        (hPartOld h a b).mpr hab
      change
        oldRawReferenceOnBase Praw e
          (Classical.choose (d.phi_surjective 1))
            (rho h (e a.val)) (rho h (e b.val)) =
        oldRawReferenceOnBase Praw e
          (Classical.choose (d.phi_surjective 1))
            (e a.val) (e b.val)
      rw [hOldExt h a, hOldExt h b,
        oldRawReferenceOnBase_old Praw e he,
        oldRawReferenceOnBase_old Praw e he]
      simp [RawRectanglePresentation.totalOldRawColour, hab, habNew]
    · exact hRawAInvariant h x y hx hy hxy
  obtain ⟨hPhaseE, hPhaseF, _hPhaseOld, hPhaseSafe⟩ :=
    D.relativePhaseAction_safe_of_rawOldAndOrbitSafeInvolutions
      rho Aimg hA hE hF oldRaw
      (fun x y hx hy hxy =>
        hRawBPhi x y (hAinB hx) (hAinB hy) hxy)
      (fun x y hx hy hxy =>
        hRawBReverse x y (hAinB hx) (hAinB hy) hxy)
      hRawAInvariant hSafeInvol
  have hPhaseInjective : Function.Injective ePhase := by
    intro x y heq
    exact he (congrArg Prod.fst heq)
  have hPhasePart : ∀ x y : U,
      DPhase.part (ePhase x) (ePhase y) ↔ Praw.part x y :=
    hPartEmbed
  have hPhaseOldExact : ∀ x y : U,
      oldPhase (ePhase x) (ePhase y) = Praw.totalOldRawColour x y :=
    oldRawReferenceOnBase_old Praw e he
      (Classical.choose (d.phi_surjective 1))
  have hPhasePhi : ∀ x y : V × H,
      x ∈ Set.range ePhase → y ∈ Set.range ePhase →
      ¬DPhase.part x y →
        d.phi (oldPhase x y) = DPhase.F x y := by
    intro x y hx hy hxy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact hRawBPhi (e a) (e b)
      ⟨a, rfl⟩ ⟨b, rfl⟩ hxy
  have hPhaseReverse : ∀ x y : V × H,
      x ∈ Set.range ePhase → y ∈ Set.range ePhase →
      ¬DPhase.part x y →
        oldPhase y x = d.reverse (oldPhase x y) := by
    intro x y hx hy hxy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact hRawBReverse (e a) (e b)
      ⟨a, rfl⟩ ⟨b, rfl⟩ hxy
  have hPhaseReturn : ∀ (h : H) (x y : V × H),
      x ∈ Set.range ePhase → y ∈ Set.range ePhase →
      ¬DPhase.part x y →
      rhoPhase h x ∈ Set.range ePhase →
      rhoPhase h y ∈ Set.range ePhase →
      oldPhase (rhoPhase h x) (rhoPhase h y) =
        oldPhase x y := by
    intro h x y hx hy _ hRetX hRetY
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    have hRx :
        relativePhaseAction rho Aimg hA h (e a, (1 : H)) ∈
          relativePhaseOldCopy (H := H) Bimg := by
      obtain ⟨c, hc⟩ := hRetX
      change relativePhaseAction rho Aimg hA h (e a, (1 : H)) ∈
        relativePhaseOldCopy (H := H) Bimg
      rw [← hc]
      exact ⟨⟨c, rfl⟩, rfl⟩
    have hRy :
        relativePhaseAction rho Aimg hA h (e b, (1 : H)) ∈
          relativePhaseOldCopy (H := H) Bimg := by
      obtain ⟨c, hc⟩ := hRetY
      change relativePhaseAction rho Aimg hA h (e b, (1 : H)) ∈
        relativePhaseOldCopy (H := H) Bimg
      rw [← hc]
      exact ⟨⟨c, rfl⟩, rfl⟩
    change oldRaw (rho h (e a)) (rho h (e b)) =
      oldRaw (e a) (e b)
    exact relativePhaseAction_oldRaw_returnConsistency
      rho Aimg Bimg hA oldRaw hRawAInvariantAll
      h (e a) (e b) hRx hRy
  have hPhasePartial : ∀ (T : Set U) (p : T → U),
      Function.Injective p →
      (∀ x y : T, Praw.part x.val y.val ↔ Praw.part (p x) (p y)) →
      (∀ x y : T, Praw.colour (p x) (p y) =
        Praw.colour x.val y.val) →
      ∃ theta : Equiv.Perm (V × H),
        (∀ x : T, theta (ePhase x.val) = ePhase (p x)) ∧
        (∀ x y, DPhase.part (theta x) (theta y) ↔
          DPhase.part x y) ∧
        (∀ x y, ¬DPhase.part x y →
          DPhase.F (theta x) (theta y) = DPhase.F x y) := by
    intro T p hp hTp hTc
    obtain ⟨theta, hOld, hThetaE, hThetaF⟩ :=
      hPartial T p hp hTp hTc
    exact D.phasePullback_liftIndividualOldPartial
      e T p theta hOld hThetaE hThetaF
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype H := Fintype.ofFinite _
  letI : Finite (V × H) := inferInstance
  exact Praw.exists_relativeSafeRawJointWitness_of_effectiveData_withBase
    DPhase code ePhase hPhaseInjective hPhasePart
    rhoPhase hPhaseE hPhaseF oldPhase
    hPhaseOldExact hPhasePhi hPhaseReverse
    hPhaseReturn hPhaseSafe hPhasePartial

end RawRectanglePresentation

end SemigenericEPPA
