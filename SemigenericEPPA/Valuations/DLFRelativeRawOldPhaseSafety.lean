import SemigenericEPPA.Valuations.RelativePhaseEffectiveSafety
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Relative H-phase raw safety from literal old colours and safe involutions

The phase blow-up distinguishes the *actual* old H-invariant
sector S, on which phases stay unchanged, from all fresh vertices,
whose phase H-coordinate is regular. The old H-action genuinely
preserves old raw colours, not just their effective G images.

An old-old H-swapped ordered cross-edge has a self-reversing raw
colour by original colour invariance and raw reversal; the swapping
element need not be an involution. An outside-old swapped pair,
in contrast, forces h²=1. If each genuinely swapped cross-edge
for such an H-involution belongs to a COMPLETE good congruence
orbit, then it has an actual reversal-fixed raw representative.

We package this exact case split as a single strict effective
H-action preserving E/F and every necessary raw swap fibre.
The complete-good-orbit hypothesis is LOCAL and does not say
that the set of all good effective colours is globally saturated.

This theorem does not itself provide the effective H-action on
a valuation witness for A⊆B, nor the raw-cover extension; those
are the next relative EPPA stages.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

/-- An actual old raw H-action together with only INVOLUTION
complete-good-orbit safety is sufficient for the strict
regular-phase action on the SAME pulled-back effective witness
to preserve E/F and have every reversed raw edge safely liftable.

No h²=1 is imposed for an old-sector swapped pair. -/
theorem EffectiveGeometry.relativePhaseAction_safe_of_rawOldAndOrbitSafeInvolutions
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hE : ∀ (h : H) (x y : V),
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ (h : H) (x y : V), ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (oldRaw : V → V → C)
    (hRawPhi : ∀ x y : V, x ∈ S → y ∈ S →
      ¬D.part x y → d.phi (oldRaw x y) = D.F x y)
    (hRawReverse : ∀ x y : V, x ∈ S → y ∈ S →
      ¬D.part x y → oldRaw y x = d.reverse (oldRaw x y))
    (hRawInvariant : ∀ (h : H) (x y : V),
      x ∈ S → y ∈ S → ¬D.part x y →
      oldRaw (rho h x) (rho h y) = oldRaw x y)
    (hSafeInvol : ∀ (h : H) (x y : V),
      h * h = 1 → ¬D.part x y →
      rho h x = y → rho h y = x →
      d.GoodCompleteOrbitAt (D.F x y)) :
    (∀ (h : H) (X Y : V × H),
      (D.phasePullback H).part
        (relativePhaseAction rho S hS h X)
        (relativePhaseAction rho S hS h Y) ↔
      (D.phasePullback H).part X Y) ∧
    (∀ (h : H) (X Y : V × H),
      ¬(D.phasePullback H).part X Y →
      (D.phasePullback H).F
        (relativePhaseAction rho S hS h X)
        (relativePhaseAction rho S hS h Y) =
      (D.phasePullback H).F X Y) ∧
    (∀ (h : H) (x : V), x ∈ S →
      relativePhaseAction rho S hS h (x, (1 : H)) =
        (rho h x, (1 : H))) ∧
    (∀ (h : H) (X Y : V × H),
      ¬(D.phasePullback H).part X Y →
      relativePhaseAction rho S hS h X = Y →
      relativePhaseAction rho S hS h Y = X →
      ∃ c : C,
        d.phi c = (D.phasePullback H).F X Y ∧
        d.reverse c = c) := by
  obtain ⟨hPhaseE, hPhaseF⟩ :=
    D.relativePhaseAction_preserves_effective rho S hS hE hF
  have hOldSafe : ∀ (h : H) (x y : V),
      x ∈ S → y ∈ S → ¬D.part x y →
      rho h x = y → rho h y = x →
      D.F x y ∈ d.selfReverseEffective := by
    intro h x y hx hy hxy hXY hYX
    have hraw := hRawInvariant h x y hx hy hxy
    rw [hXY, hYX] at hraw
    have hreverse : d.reverse (oldRaw x y) = oldRaw x y := by
      calc
        d.reverse (oldRaw x y) = oldRaw y x :=
          (hRawReverse x y hx hy hxy).symm
        _ = oldRaw x y := hraw
    exact ⟨oldRaw x y, hRawPhi x y hx hy hxy, hreverse⟩
  have hInvSafe : ∀ (h : H) (x y : V),
      h * h = 1 → ¬D.part x y →
      rho h x = y → rho h y = x →
      D.F x y ∈ d.selfReverseEffective := by
    intro h x y htwo hxy hXY hYX
    exact d.good_of_completeOrbitAt (D.F x y)
      (hSafeInvol h x y htwo hxy hXY hYX)
  have hPhaseSafe :=
    D.relativePhaseAction_allFlipsSafe_of_sectorSafety
      d rho S hS hOldSafe hInvSafe
  exact ⟨hPhaseE, hPhaseF,
    fun h x hx => relativePhaseAction_old rho S hS h x hx,
    hPhaseSafe⟩

end SemigenericEPPA
