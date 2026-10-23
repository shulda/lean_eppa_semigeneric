import SemigenericEPPA.Bridge.OrbitSaturationPrescribedReversal
import SemigenericEPPA.Bridge.PrescribedGroupInvariantRawOrbits

/-!
# H-invariant raw colours with NONINVARIANT prescribed old subset

The existing orbit-colour theorem assumes its prescribed old
subset is H-invariant. In relative safe EPPA the distinguished
phase-one copy of B is NOT invariant because H acts only on
A⊆B and phases are regular outside A.

The correct hypothesis is return consistency: whenever an H
translate of a prescribed old directed edge lands back inside
the prescribed old edge set, its original raw colour is
unchanged. We first saturate this arbitrary old subset under
H, extend its raw colours invariantly, and prove the extended
prescribed colours reverse correctly on the entire saturation.
Only then do we invoke the certified invariant/reversal orbit
selection theorem on the H-invariant saturation.

Any H-reversed orbit lying OUTSIDE the saturation must possess
a raw reversal-fixed representative over its effective colour;
this is exactly the relative safe H-action flip condition.

This gives the needed general finite raw H-orbit selection:
* exact φ-projection of every raw colour;
* literal reversal and H invariance globally;
* all originally prescribed B raw colours preserved exactly;
* NO a priori H invariance of the original B prescribed subset;
* NO global congruence saturation, no normality or abelian G.

The later phase/base/witness construction must discharge the
return and swap-safety hypotheses from actual geometry.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G]
variable {C : Type w} {A : Type t}

/-- Raw orbit colouring of an arbitrary finite H-set, with an
H-equivariant effective colour map and commuting reversal.
Unlike the earlier invariant-subset extension theorem the
original prescribed S can move outside itself under H. -/
theorem exists_groupInvariantRawOrbitColour_extendingNonInvariantSubset
    [Finite A]
    (d : RawDatum G C)
    (rho : H →* Equiv.Perm A)
    (tau : A → A) (htau : Function.Involutive tau)
    (hCommute : ∀ (h : H) (a : A),
      tau (rho h a) = rho h (tau a))
    (f : A → G)
    (hfInvariant : ∀ (h : H) (a : A),
      f (rho h a) = f a)
    (hfReverse : ∀ a : A,
      f (tau a) = d.s (f a))
    (S : Set A)
    (hSrev : ∀ a : A, a ∈ S ↔ tau a ∈ S)
    (old : A → C)
    (hOldPhi : ∀ a : A, a ∈ S → d.phi (old a) = f a)
    (hOldReverse : ∀ a : A, a ∈ S →
      old (tau a) = d.reverse (old a))
    (hReturn : ∀ (h : H) (a : A),
      a ∈ S → rho h a ∈ S →
      old (rho h a) = old a)
    (hSafeNew : ∀ a : A,
      a ∉ orbitSaturation rho S →
      (∃ h : H, rho h a = tau a) →
      ∃ c : C, d.phi c = f a ∧ d.reverse c = c) :
    ∃ colour : A → C,
      (∀ a : A, d.phi (colour a) = f a) ∧
      (∀ a : A, colour (tau a) = d.reverse (colour a)) ∧
      (∀ (h : H) (a : A),
        colour (rho h a) = colour a) ∧
      (∀ a : A, a ∈ S → colour a = old a) := by
  classical
  letI : Nonempty C := ⟨Classical.choose (d.phi_surjective 1)⟩
  obtain ⟨oldSat, hOldS, hOldH, hOldRevSat⟩ :=
    exists_invariantReversingColour_on_orbitSaturation
      rho tau hCommute d.reverse S hSrev
      old hOldReverse hReturn
  let SS : Set A := orbitSaturation rho S
  have hSSrev : ∀ a : A, a ∈ SS ↔ tau a ∈ SS :=
    orbitSaturation_reverse_iff rho tau htau hCommute S hSrev
  have hSSinvariant : ∀ (h : H) (a : A),
      a ∈ SS ↔ rho h a ∈ SS := by
    intro h a
    constructor
    · exact orbitSaturation_stable rho S h a
    · intro ha
      have hh : rho h⁻¹ (rho h a) ∈ SS :=
        orbitSaturation_stable rho S h⁻¹ (rho h a) ha
      have heq : rho h⁻¹ (rho h a) = a := by
        calc
          rho h⁻¹ (rho h a) = rho (h⁻¹ * h) a := by
            rw [map_mul]
            rfl
          _ = a := by simp
      rwa [heq] at hh
  have hOldPhiSat : ∀ a : A, a ∈ SS →
      d.phi (oldSat a) = f a := by
    intro a ha
    obtain ⟨b, hb, h, hba⟩ := ha
    calc
      d.phi (oldSat a) = d.phi (oldSat (rho h b)) := by rw [hba]
      _ = d.phi (oldSat b) := congrArg d.phi (hOldH h b)
      _ = d.phi (old b) := by rw [hOldS b hb]
      _ = f b := hOldPhi b hb
      _ = f (rho h b) := (hfInvariant h b).symm
      _ = f a := by rw [hba]
  have hOldHsat : ∀ (h : H) (a : A), a ∈ SS →
      oldSat (rho h a) = oldSat a := by
    intro h a _
    exact hOldH h a
  obtain ⟨colour, hPhi, hReverse, hInvariant, hExtSat⟩ :=
    exists_groupInvariantRawOrbitColour_extendingSubset
      d rho tau htau hCommute f hfInvariant hfReverse
      SS hSSrev hSSinvariant oldSat hOldPhiSat
      hOldRevSat hOldHsat hSafeNew
  refine ⟨colour, hPhi, hReverse, hInvariant, ?_⟩
  intro a ha
  calc
    colour a = oldSat a :=
      hExtSat a (mem_orbitSaturation_of_mem rho S a ha)
    _ = old a := hOldS a ha

end SemigenericEPPA
