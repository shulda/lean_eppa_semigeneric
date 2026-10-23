import SemigenericEPPA.Structure.RelativePhaseNonInvariantRawCoverGroupLift
import SemigenericEPPA.Valuations.DLFPhaseOldReturnConsistency

/-!
# Relative safe H-phase group lift preserving a noninvariant B-copy

Suppose H acts on a distinguished old A⊆B, and D is an effective
finite witness with H acting on its entire vertex set and preserving
E/F. The set A is H-invariant but the prescribed larger set B is
not required to be invariant. Assume original raw B colours are
correct and reverse under raw reversal, and the H-action genuinely
preserves raw colours only on A×A.

Take the phase-one B-copy T={(x,1): x∈B} in D×H. The audited
phase-return lemma proves raw return consistency automatically:
if an H-translate of an old B-cross-pair returns to B-phase one,
then either h=1 or both bases lie in A. No invariance of any
B\A raw colour is required.

The phase + noninvariant raw-cover theorem then constructs a
single finite raw residual cover of D×H and an honest strict
H-action preserving E and all original R_c, transporting ALL zero
section points, while retaining EVERY literal raw B-colour on
the distinguished phase-one zero section.

This theorem still assumes the chosen effective D-action is
safe on swapped pairs for actual H-involutions. The remaining
relative safe EPPA work constructs that action and individual
partial extensions for B on the SAME effective witness.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H] [Finite H]
variable {L : Type z} [AddCommGroup L] {d : RawDatum G C}

/-- Actual original B-phase one raw colours survive inside an
H-equivariant finite raw cover without requiring B to be
H-invariant. The exact B-return condition is DERIVED from the
regular phase action, not assumed. -/
theorem EffectiveGeometry.exists_relativePhaseOneRawCover_forOldB
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (rho : H →* Equiv.Perm V)
    (A B : Set V) (hAB : A ⊆ B)
    (hA : ∀ (h : H) (x : V), x ∈ A ↔ rho h x ∈ A)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (oldRaw : V → V → C)
    (hBPhi : ∀ x y, x ∈ B → y ∈ B →
      ¬D.part x y → d.phi (oldRaw x y) = D.F x y)
    (hBReverse : ∀ x y, x ∈ B → y ∈ B →
      ¬D.part x y → oldRaw y x = d.reverse (oldRaw x y))
    (hAInvariant : ∀ h : H, ∀ x y,
      x ∈ A → y ∈ A →
      oldRaw (rho h x) (rho h y) = oldRaw x y)
    (hSafeInvol : ∀ (h : H) (x y : V),
      h * h = 1 → ¬D.part x y →
      rho h x = y → rho h y = x →
      d.GoodCompleteOrbitAt (D.F x y)) :
    Finite (RawCoverVertex (V × H) L) ∧
    ∃ (b : (V × H) → (V × H) → L)
      (hb : ∀ X Y, ¬(D.phasePullback H).part X Y →
        b Y X = code.shift ((D.phasePullback H).F X Y) - b X Y)
      (lift : H →* Equiv.Perm (RawCoverVertex (V × H) L)),
      (∀ X Y : V × H,
        X ∈ relativePhaseOldCopy (H := H) B →
        Y ∈ relativePhaseOldCopy (H := H) B →
        ¬(D.phasePullback H).part X Y →
        b X Y = code.encodeRaw (oldRaw X.1 Y.1)) ∧
      (∀ X Y : V × H,
        X ∈ relativePhaseOldCopy (H := H) B →
        Y ∈ relativePhaseOldCopy (H := H) B →
        ¬(D.phasePullback H).part X Y →
        rawCoverColour (D.phasePullback H) code b
          (X, fun _ : V × H => (0 : L))
          (Y, fun _ : V × H => (0 : L)) =
          some (oldRaw X.1 Y.1)) ∧
      (∀ h : H, ∀ X : V × H,
        lift h (X, fun _ : V × H => (0 : L)) =
          (relativePhaseAction rho A hA h X,
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
  let T : Set (V × H) := relativePhaseOldCopy (H := H) B
  let oldPhase : (V × H) → (V × H) → C :=
    fun X Y => oldRaw X.1 Y.1
  have hAPhi : ∀ x y : V, x ∈ A → y ∈ A →
      ¬D.part x y → d.phi (oldRaw x y) = D.F x y := by
    intro x y hx hy hxy
    exact hBPhi x y (hAB hx) (hAB hy) hxy
  have hAReverse : ∀ x y : V, x ∈ A → y ∈ A →
      ¬D.part x y → oldRaw y x = d.reverse (oldRaw x y) := by
    intro x y hx hy hxy
    exact hBReverse x y (hAB hx) (hAB hy) hxy
  have hAPreserve (h : H) (x y : V)
      (hx : x ∈ A) (hy : y ∈ A) (hxy : ¬D.part x y) :
      oldRaw (rho h x) (rho h y) = oldRaw x y :=
    hAInvariant h x y hx hy
  have hTPhi : ∀ X Y : V × H,
      X ∈ T → Y ∈ T →
      ¬(D.phasePullback H).part X Y →
      d.phi (oldPhase X Y) = (D.phasePullback H).F X Y := by
    intro X Y hx hy hxy
    exact hBPhi X.1 Y.1 hx.1 hy.1 hxy
  have hTReverse : ∀ X Y : V × H,
      X ∈ T → Y ∈ T →
      ¬(D.phasePullback H).part X Y →
      oldPhase Y X = d.reverse (oldPhase X Y) := by
    intro X Y hx hy hxy
    exact hBReverse X.1 Y.1 hx.1 hy.1 hxy
  have hTReturn : ∀ h : H, ∀ X Y : V × H,
      X ∈ T → Y ∈ T →
      ¬(D.phasePullback H).part X Y →
      relativePhaseAction rho A hA h X ∈ T →
      relativePhaseAction rho A hA h Y ∈ T →
      oldPhase (relativePhaseAction rho A hA h X)
        (relativePhaseAction rho A hA h Y) = oldPhase X Y := by
    intro h X Y hx hy hxy htx hty
    have hX : X = (X.1, (1 : H)) :=
      Prod.ext rfl hx.2
    have hY : Y = (Y.1, (1 : H)) :=
      Prod.ext rfl hy.2
    have htx' :
        relativePhaseAction rho A hA h (X.1, (1 : H)) ∈ T := by
      simpa only [← hX] using htx
    have hty' :
        relativePhaseAction rho A hA h (Y.1, (1 : H)) ∈ T := by
      simpa only [← hY] using hty
    change oldRaw (rho h X.1) (rho h Y.1) =
      oldRaw X.1 Y.1
    exact relativePhaseAction_oldRaw_returnConsistency
      rho A B hA oldRaw hAInvariant h X.1 Y.1 htx' hty'
  exact D.exists_relativePhaseNonInvariantRawCoverGroupLift
    code rho A hA hE hF oldRaw
    hAPhi hAReverse hAPreserve hSafeInvol
    T oldPhase hTPhi hTReverse hTReturn

end SemigenericEPPA
