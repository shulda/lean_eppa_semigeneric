import SemigenericEPPA.Structure.RawCoverPotentialGroupAction
import SemigenericEPPA.Valuations.RelativePhaseEffectiveSafety
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Local DLF involution safety survives relative phases and raw potentials

The positive DLF proof does NOT need global congruence saturation.
It needs the colour-specific predicate GoodCompleteOrbitAt on each
effective cross-E pair reversed by an actual involution in the
prescribed finite group.

Two further constructions preserve this condition automatically:
* regular phase blow-up changes neither base effective colour nor
  the first-coordinate action of H;
* an affine-potential raw-cover lift also acts on the first coordinate
  by the prescribed base permutation.

We prove the exact first-coordinate equation for arbitrary
potential lifts and the resulting involution-safety transport
for both constructions. These lemmas avoid a false inference from
raw colour self-reversal alone: GOOD means an ENTIRE affine
congruence orbit is good, strictly stronger than one reversal-fixed
raw representative.

A finite relative raw-cover theorem must subsequently expose
the actual first-coordinate action of its selected lift.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- An involution-safe effective H action remains safe with respect
to COMPLETE good congruence orbits on the phase-blown-up geometry,
regardless of the phase coordinates or old/non-old sector. -/
theorem relativePhaseAction_involutionCompleteOrbitSafe
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (S : Set V)
    (hS : ∀ (h : H) (x : V), x ∈ S ↔ rho h x ∈ S)
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬D.part x y →
        rho h x = y → rho h y = x →
          d.GoodCompleteOrbitAt (D.F x y))
    (h : H) (htwo : h * h = 1)
    (X Y : V × H)
    (hcross : ¬(D.phasePullback H).part X Y)
    (hxy : relativePhaseAction rho S hS h X = Y)
    (hyx : relativePhaseAction rho S hS h Y = X) :
    d.GoodCompleteOrbitAt ((D.phasePullback H).F X Y) := by
  have hbXY : rho h X.1 = Y.1 :=
    (relativePhaseAction_base rho S hS h X).symm.trans
      (congrArg Prod.fst hxy)
  have hbYX : rho h Y.1 = X.1 :=
    (relativePhaseAction_base rho S hS h Y).symm.trans
      (congrArg Prod.fst hyx)
  exact hSafe h htwo X.1 Y.1 hcross hbXY hbYX

end EffectiveGeometry

/-- Potential corrections do not alter the first vertex component
of the actual homomorphic action on a raw residual cover. -/
@[simp] theorem rawCoverPotentialGroupLift_base
    {L : Type*} [AddCommGroup L]
    (nu : V → V → L)
    (rho : H →* Equiv.Perm V)
    (h : H) (X : RawCoverVertex V L) :
    (rawCoverPotentialGroupLift nu rho h X).1 = rho h X.1 := rfl

/-- For EVERY complete-good-orbit-safe involution of the effective
base action, its potential-based raw-cover lift inherits the SAME
safety predicate on crossed effective base vertices.

This does not use full global saturation or assume that every
self-reversing raw colour has a complete good orbit. -/
theorem rawCoverPotentialGroupLift_involutionCompleteOrbitSafe
    {L : Type*} [AddCommGroup L]
    (D : EffectiveGeometry d.s V)
    (nu : V → V → L)
    (rho : H →* Equiv.Perm V)
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬D.part x y →
        rho h x = y → rho h y = x →
          d.GoodCompleteOrbitAt (D.F x y))
    (h : H) (htwo : h * h = 1)
    (X Y : RawCoverVertex V L)
    (hcross : ¬D.part X.1 Y.1)
    (hxy : rawCoverPotentialGroupLift nu rho h X = Y)
    (hyx : rawCoverPotentialGroupLift nu rho h Y = X) :
    d.GoodCompleteOrbitAt (D.F X.1 Y.1) := by
  have hbXY : rho h X.1 = Y.1 := by
    have h := congrArg Prod.fst hxy
    simpa only [rawCoverPotentialGroupLift_base] using h
  have hbYX : rho h Y.1 = X.1 := by
    have h := congrArg Prod.fst hyx
    simpa only [rawCoverPotentialGroupLift_base] using h
  exact hSafe h htwo X.1 Y.1 hcross hbXY hbYX

end SemigenericEPPA
