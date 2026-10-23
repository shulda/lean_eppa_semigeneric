import SemigenericEPPA.Valuations.RelativeRegularPhaseGroupAction
import SemigenericEPPA.Structure.EffectiveGeometry

/-!
# Relative safe H-actions after a regular phase blow-up

The phase-expanded carrier V×H inherits its E and effective
F from V via first projection. The strict relative action is
 (h·x,r) on the invariant old sector S and
 (h·x,h*r) outside S.

This file proves the EXACT two-sector flip-safety interface:
* on old-old swapped pairs, safety follows directly from the
  prescribed old raw action, and h need not be an involution;
* any swapped pair with an endpoint outside S has both bases
  outside S and necessarily h²=1, so its safety follows from
  an involution-only assumption on the underlying effective
  group action.

No globally saturated good set is assumed. In the ultimate DLF
application, safety of those base involutions will follow from
one complete good affine congruence orbit, not global saturation.
The raw fibre cover and full relative EPPA remain separate.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]

namespace EffectiveGeometry

/-- Reindex the exact E/F rectangle geometry onto phase copies
without adding new effective colours or any orientation. -/
def phasePullback
    (D : EffectiveGeometry (s : AffineAntiInvolution G) V)
    (H : Type t) : EffectiveGeometry s (V × H) where
  part := {
    r := fun X Y => D.part X.1 Y.1
    iseqv := by
      constructor
      · intro X
        exact D.part.iseqv.refl X.1
      · intro X Y h
        exact D.part.iseqv.symm h
      · intro X Y Z hXY hYZ
        exact D.part.iseqv.trans hXY hYZ
  }
  F := fun X Y => D.F X.1 Y.1
  reverse_cross := by
    intro X Y hCross
    exact D.reverse_cross X.1 Y.1 hCross
  rectangle := by
    intro X₀ X₁ Y₀ Y₁ hX hY hCross
    exact D.rectangle X₀.1 X₁.1 Y₀.1 Y₁.1 hX hY hCross

@[simp] theorem phasePullback_part
    (D : EffectiveGeometry (s : AffineAntiInvolution G) V)
    (X Y : V × H) :
    D.phasePullback H |>.part X Y ↔ D.part X.1 Y.1 := Iff.rfl

@[simp] theorem phasePullback_F
    (D : EffectiveGeometry (s : AffineAntiInvolution G) V)
    (X Y : V × H) :
    (D.phasePullback H).F X Y = D.F X.1 Y.1 := rfl

/-- The strict phase action preserves the pulled-back E/F
geometry whenever the original H-action preserves D. -/
theorem relativePhaseAction_preserves_effective
    (D : EffectiveGeometry (s : AffineAntiInvolution G) V)
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hE : ∀ (h : H) (x y : V),
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ (h : H) (x y : V), ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y) :
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
      (D.phasePullback H).F X Y) := by
  constructor
  · intro h X Y
    change D.part (rho h X.1) (rho h Y.1) ↔
      D.part X.1 Y.1
    exact hE h X.1 Y.1
  · intro h X Y hXY
    change D.F (rho h X.1) (rho h Y.1) =
      D.F X.1 Y.1
    exact hF h X.1 Y.1 hXY

/-- The precise relative phase raw flip-safety reduction.
Old-old swaps (possibly by elements of order >2) and
outside-old swaps (only by involutions) are treated separately.

For the real DLF proof the old-sector safety comes from the
prescribed raw H-action; the outside-sector involution safety
must be derived from the one complete good congruence orbit. -/
theorem relativePhaseAction_allFlipsSafe_of_sectorSafety
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hOldSafe : ∀ (h : H) (x y : V),
      x ∈ S → y ∈ S → ¬D.part x y →
      rho h x = y → rho h y = x →
      D.F x y ∈ d.selfReverseEffective)
    (hOutsideInvolutionSafe : ∀ (h : H) (x y : V),
      h * h = 1 → ¬D.part x y →
      rho h x = y → rho h y = x →
      D.F x y ∈ d.selfReverseEffective) :
    ∀ (h : H) (X Y : V × H),
      ¬(D.phasePullback H).part X Y →
      relativePhaseAction rho S hS h X = Y →
      relativePhaseAction rho S hS h Y = X →
      ∃ c : C,
        d.phi c = (D.phasePullback H).F X Y ∧
        d.reverse c = c := by
  intro h X Y hCross hXY hYX
  have hbXY : rho h X.1 = Y.1 :=
    (relativePhaseAction_base rho S hS h X).symm.trans
      (congrArg Prod.fst hXY)
  have hbYX : rho h Y.1 = X.1 :=
    (relativePhaseAction_base rho S hS h Y).symm.trans
      (congrArg Prod.fst hYX)
  have hGood : D.F X.1 Y.1 ∈ d.selfReverseEffective := by
    by_cases hx : X.1 ∈ S
    · have hy : Y.1 ∈ S := by
        rw [← hbXY]
        exact (hS h X.1).mp hx
      exact hOldSafe h X.1 Y.1 hx hy hCross hbXY hbYX
    · have hTwo : h * h = 1 :=
        relativePhaseAction_swapOutside_square_one
          rho S hS h X Y hx hXY hYX
      exact hOutsideInvolutionSafe h X.1 Y.1 hTwo hCross hbXY hbYX
  exact hGood

end EffectiveGeometry

end SemigenericEPPA
