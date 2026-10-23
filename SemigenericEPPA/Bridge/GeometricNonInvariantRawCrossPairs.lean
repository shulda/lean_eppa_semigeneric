import SemigenericEPPA.Bridge.GeometricPrescribedRawCrossPairs
import SemigenericEPPA.Bridge.NonInvariantPrescribedRawOrbitSelection

/-!
# Geometric raw-colour extension from a NON-H-invariant old B-copy

The relative safe-group EPPA construction starts with finite A⊆B,
but only H≤Aut(A), not an H-action on B. Its phase-one B-copy
inside the effective valuation witness is therefore NOT H-invariant.
Prescribed old raw edge colours must nevertheless be preserved.

The correct orbit hypothesis is exact return consistency: if
both endpoints of a prescribed B-cross pair and their H-translates
again lie in B, the raw colours match. If any H action reverses
an effective cross pair outside the saturation of those prescribed
pairs, a self-reversing raw representative must exist.

Apply the certified noninvariant prescribed orbit saturation,
reversal transport and raw orbit selection to the actual set of
all directed effective cross pairs. We obtain a globally H-invariant,
reversal-compatible raw-colour refinement extending every
prescribed original edge LITERALLY.

This removes the incorrect old H-invariance assumption from the
raw side of relative DLF. The existence of the underlying safe
H-action for arbitrary A⊆B, and individual partial-map extensions
on the same subsequent raw cover, are still independent tasks.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- Global H-invariant original raw colour refinement extending a
possibly NONINVARIANT old vertex subset, with only literal
old raw-colour return consistency and safety on reversed orbits. -/
theorem exists_groupInvariantRawCrossColour_extendingNonInvariantSubset
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (S : Set V)
    (old : V → V → C)
    (hOldPhi : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hOldReverse : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → old y x = d.reverse (old x y))
    (hOldInvariant : ∀ h : H, ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      old (rho h x) (rho h y) = old x y)
    (hOldReturn : ∀ h : H, ∀ x y : V,
      x ∈ S → y ∈ S → ¬D.part x y →
      rho h x ∈ S → rho h y ∈ S →
      old (rho h x) (rho h y) = old x y)
    (hSafeAll : ∀ h : H, ∀ x y,
      ¬D.part x y →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    ∃ colour : V → V → C,
      (∀ x y, ¬D.part x y →
        d.phi (colour x y) = D.F x y) ∧
      (∀ x y, ¬D.part x y →
        colour y x = d.reverse (colour x y)) ∧
      (∀ h : H, ∀ x y, ¬D.part x y →
        colour (rho h x) (rho h y) = colour x y) ∧
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        colour x y = old x y) := by
  classical
  let A := EffectiveCrossPair D
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype A := inferInstance
  let action : H →* Equiv.Perm A :=
    effectiveCrossPairAction D rho hE
  let tau : A → A := effectiveCrossPairReverse D
  let f : A → G := fun p => D.F p.val.1 p.val.2
  let Sold : Set A := {p | p.val.1 ∈ S ∧ p.val.2 ∈ S}
  let oldPair : A → C := fun p => old p.val.1 p.val.2
  have hCommute : ∀ (h : H) (p : A),
      tau (action h p) = action h (tau p) := by
    intro h p
    apply Subtype.ext
    rfl
  have hInvariant : ∀ (h : H) (p : A),
      f (action h p) = f p := by
    intro h p
    exact hF h p.val.1 p.val.2 p.property
  have hReverse : ∀ p : A, f (tau p) = d.s (f p) := by
    intro p
    exact D.reverse_cross p.val.1 p.val.2 p.property
  have hSoldRev : ∀ p : A, p ∈ Sold ↔ tau p ∈ Sold := by
    intro p
    change (p.val.1 ∈ S ∧ p.val.2 ∈ S) ↔
      (p.val.2 ∈ S ∧ p.val.1 ∈ S)
    exact and_comm
  have hOldPairPhi :
      ∀ p : A, p ∈ Sold → d.phi (oldPair p) = f p := by
    intro p hp
    exact hOldPhi p.val.1 p.val.2 hp.1 hp.2 p.property
  have hOldPairRev :
      ∀ p : A, p ∈ Sold →
        oldPair (tau p) = d.reverse (oldPair p) := by
    intro p hp
    exact hOldReverse p.val.1 p.val.2 hp.1 hp.2 p.property
  have hOldPairReturn :
      ∀ (h : H) (p : A), p ∈ Sold →
        action h p ∈ Sold →
        oldPair (action h p) = oldPair p := by
    intro h p hp htarget
    exact hOldReturn h p.val.1 p.val.2
      hp.1 hp.2 p.property htarget.1 htarget.2
  have hSafePairs : ∀ p : A, p ∉ orbitSaturation action Sold →
      (∃ h : H, action h p = tau p) →
      ∃ c : C, d.phi c = f p ∧ d.reverse c = c := by
    intro p _ ⟨h, hswap⟩
    have hswap' := congrArg Subtype.val hswap
    have hx : rho h p.val.1 = p.val.2 :=
      congrArg Prod.fst hswap'
    have hy : rho h p.val.2 = p.val.1 :=
      congrArg Prod.snd hswap'
    exact hSafeAll h p.val.1 p.val.2 p.property hx hy
  obtain ⟨edgeColour, hPhi, hRev, hInv, hOld⟩ :=
    exists_groupInvariantRawOrbitColour_extendingNonInvariantSubset
      d action tau (effectiveCrossPairReverse_involutive D)
      hCommute f hInvariant hReverse Sold
      hSoldRev oldPair hOldPairPhi
      hOldPairRev hOldPairReturn hSafePairs
  let default : C := Classical.choose (d.phi_surjective 1)
  let colour : V → V → C := fun x y =>
    if hxy : ¬D.part x y then
      edgeColour ⟨(x,y),hxy⟩ else default
  have hc (x y : V) (hxy : ¬D.part x y) :
      colour x y = edgeColour ⟨(x,y),hxy⟩ := by
    simp [colour, hxy]
  refine ⟨colour, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hc x y hxy]
    exact hPhi ⟨(x,y),hxy⟩
  · intro x y hxy
    have hyx : ¬D.part y x := by
      intro h
      exact hxy (D.part.iseqv.symm h)
    have h := hRev ⟨(x,y),hxy⟩
    change edgeColour ⟨(y,x),hyx⟩ =
      d.reverse (edgeColour ⟨(x,y),hxy⟩) at h
    rw [hc y x hyx, hc x y hxy]
    exact h
  · intro h x y hxy
    have hxy' : ¬D.part (rho h x) (rho h y) := by
      intro hh
      exact hxy ((hE h x y).mp hh)
    have hInvEq := hInv h ⟨(x,y),hxy⟩
    change edgeColour ⟨(rho h x,rho h y),hxy'⟩ =
      edgeColour ⟨(x,y),hxy⟩ at hInvEq
    rw [hc (rho h x) (rho h y) hxy', hc x y hxy]
    exact hInvEq
  · intro x y hx hy hxy
    have hold : (⟨(x,y),hxy⟩ : A) ∈ Sold :=
      ⟨hx,hy⟩
    rw [hc x y hxy]
    exact hOld ⟨(x,y),hxy⟩ hold

end SemigenericEPPA
