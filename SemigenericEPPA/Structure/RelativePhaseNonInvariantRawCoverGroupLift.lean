import SemigenericEPPA.Structure.NonInvariantPrescribedRawCoverGroupLift
import SemigenericEPPA.Valuations.DLFRelativeRawOldPhaseSafety

/-!
# The COMPLETE relative phase action lifts to one finite raw cover

Assume a strict effective H-action on a finite base D preserving
E/F, an H-invariant old sector A whose original raw colours
are genuinely preserved by H, and complete-good-orbit safety for
swapped cross-E pairs under actual involutions of H.

The relative phase construction on D×H uses trivial phase over
A and regular phase elsewhere. Its previously certified exact
case split gives genuine effective E/F preservation and raw
flip safety under EVERY H element. In the first case, even an
element of order four may swap an old raw pair; in the second,
the regular phase forces h²=1.

Now let T be ANY prescribed raw-coloured vertex subset in D×H,
not assumed H-invariant (the intended case is the phase-one copy
of a larger B containing A). Suppose the original T raw colours
are return-consistent whenever their H-translates land back in T.

The noninvariant orbit theorem constructs one globally invariant
raw refinement; using it as the full affine-code baseline produces
a finite raw cover and a STRICT H→Aut action on its ENTIRE zero
section, preserving all old T colours literally. This avoids any
incorrect assumption that H acts by automorphisms on B.

This is the relative phase + raw GROUP lift gate. It does NOT yet
construct a relative effective witness for arbitrary A⊆B, nor
supply individual B partial automorphism extensions on this same
raw cover.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w}
variable {H : Type t} [Group H] [Finite H]
variable {L : Type z} [AddCommGroup L]
variable {d : RawDatum G C}

/-- An H-safe relative phase geometry with NONINVARIANT prescribed
raw copy T admits one finite genuine H-equivariant original raw
cover. H acts homomorphically on the complete zero section, and
the old raw T edge colours are retained without any H action on T. -/
theorem EffectiveGeometry.exists_relativePhaseNonInvariantRawCoverGroupLift
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (oldRaw : V → V → C)
    (hRawPhi : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → d.phi (oldRaw x y) = D.F x y)
    (hRawReverse : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → oldRaw y x = d.reverse (oldRaw x y))
    (hRawInvariant : ∀ (h : H) (x y : V),
      x ∈ S → y ∈ S → ¬D.part x y →
      oldRaw (rho h x) (rho h y) = oldRaw x y)
    (hSafeInvol : ∀ (h : H) (x y : V),
      h * h = 1 → ¬D.part x y →
      rho h x = y → rho h y = x →
      d.GoodCompleteOrbitAt (D.F x y))
    (T : Set (V × H))
    (oldPhase : (V × H) → (V × H) → C)
    (hTPhi : ∀ x y, x ∈ T → y ∈ T →
      ¬(D.phasePullback H).part x y →
      d.phi (oldPhase x y) = (D.phasePullback H).F x y)
    (hTReverse : ∀ x y, x ∈ T → y ∈ T →
      ¬(D.phasePullback H).part x y →
      oldPhase y x = d.reverse (oldPhase x y))
    (hTReturn : ∀ h : H, ∀ x y,
      x ∈ T → y ∈ T →
      ¬(D.phasePullback H).part x y →
      relativePhaseAction rho S hS h x ∈ T →
      relativePhaseAction rho S hS h y ∈ T →
      oldPhase
        (relativePhaseAction rho S hS h x)
        (relativePhaseAction rho S hS h y) = oldPhase x y) :
    Finite (RawCoverVertex (V × H) L) ∧
    ∃ (b : (V × H) → (V × H) → L)
      (hb : ∀ x y, ¬(D.phasePullback H).part x y →
        b y x = code.shift ((D.phasePullback H).F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex (V × H) L)),
      (∀ x y, x ∈ T → y ∈ T →
        ¬(D.phasePullback H).part x y →
        b x y = code.encodeRaw (oldPhase x y)) ∧
      (∀ x y, x ∈ T → y ∈ T →
        ¬(D.phasePullback H).part x y →
        rawCoverColour (D.phasePullback H) code b
          (x, fun _ : V × H => (0 : L))
          (y, fun _ : V × H => (0 : L)) = some (oldPhase x y)) ∧
      (∀ h : H, ∀ x : V × H,
        lift h (x, fun _ : V × H => (0 : L)) =
          (relativePhaseAction rho S hS h x,
            fun _ : V × H => (0 : L))) ∧
      (∀ h : H, ∀ X Y : RawCoverVertex (V × H) L,
        (D.phasePullback H).part (lift h X).1 (lift h Y).1 ↔
          (D.phasePullback H).part X.1 Y.1) ∧
      (∀ h : H, ∀ c : C, ∀ X Y : RawCoverVertex (V × H) L,
        rawRel
          (rawCoverPresentation (D.phasePullback H) code b hb).toStructure
          c (lift h X) (lift h Y) ↔
        rawRel
          (rawCoverPresentation (D.phasePullback H) code b hb).toStructure
          c X Y) := by
  classical
  letI : Finite (V × H) := inferInstance
  obtain ⟨hPhaseE, hPhaseF, _hOldZeroPhase, hPhaseSafe⟩ :=
    D.relativePhaseAction_safe_of_rawOldAndOrbitSafeInvolutions
      rho S hS hE hF oldRaw
      hRawPhi hRawReverse hRawInvariant hSafeInvol
  exact exists_nonInvariantPrescribedRawCoverGroupLift
    (D.phasePullback H) code
    (relativePhaseAction rho S hS) hPhaseE hPhaseF
    T oldPhase hTPhi hTReverse hTReturn hPhaseSafe

end SemigenericEPPA
