import SemigenericEPPA.Bridge.GeometricInvariantRawCrossPairs
import SemigenericEPPA.Bridge.PrescribedGroupInvariantRawOrbits

/-!
# Geometric H-invariant raw colours extending an actual old substructure

The existing orbit-colour extension theorem works on a finite
H-set with commuting reversal; the geometric cross-pair theorem
instantiates the unrestricted case on the actual ordered pairs
(x,y) with ¬E(x,y). Here we combine both steps with a *nonempty*
old vertex set S.

Assume H acts by genuine effective E/F automorphisms, S is stable
under H, and the old raw colours on pairs from S are already
H-invariant, reverse correctly and project to effective F.
On new reversal orbits only, the endpoint-swap safety condition
supplies a self-reversing raw representative when needed.

We obtain one global raw-colour refinement of F, preserving the
literal old raw colours as well as H-invariance and reversal.
No relative DLF or coherent EPPA conclusion is asserted here.
-/

namespace SemigenericEPPA

universe u v w t

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- Exact raw-colour extension on all directed cross-E pairs:
old-old colours are retained pointwise, and no self-reversing
colour is required for old orbits because their H-invariance
and reversal consistency already imply the needed compatibility. -/
theorem exists_groupInvariantRawCrossColour_extendingSubset
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (S : Set V)
    (hS : ∀ h : H, ∀ x : V, x ∈ S → rho h x ∈ S)
    (old : V → V → C)
    (hOldPhi : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hOldReverse : ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y → old y x = d.reverse (old x y))
    (hOldInvariant : ∀ h : H, ∀ x y, x ∈ S → y ∈ S →
      ¬D.part x y →
      old (rho h x) (rho h y) = old x y)
    (hSafeNew : ∀ h : H, ∀ x y,
      ¬D.part x y → ¬(x ∈ S ∧ y ∈ S) →
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
  have hSiff (h : H) (x : V) :
      x ∈ S ↔ rho h x ∈ S := by
    constructor
    · exact hS h x
    · intro hx
      have hy := hS h⁻¹ (rho h x) hx
      have hinv : rho h⁻¹ (rho h x) = x := by
        calc
          rho h⁻¹ (rho h x) = rho (h⁻¹ * h) x := by
            rw [map_mul]
            rfl
          _ = x := by simp
      exact hinv ▸ hy
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
  have hSoldGroup :
      ∀ (h : H) (p : A), p ∈ Sold ↔ action h p ∈ Sold := by
    intro h p
    change (p.val.1 ∈ S ∧ p.val.2 ∈ S) ↔
      (rho h p.val.1 ∈ S ∧ rho h p.val.2 ∈ S)
    exact and_congr (hSiff h p.val.1) (hSiff h p.val.2)
  have hOldPairPhi :
      ∀ p : A, p ∈ Sold → d.phi (oldPair p) = f p := by
    intro p hp
    exact hOldPhi p.val.1 p.val.2 hp.1 hp.2 p.property
  have hOldPairRev :
      ∀ p : A, p ∈ Sold →
        oldPair (tau p) = d.reverse (oldPair p) := by
    intro p hp
    exact hOldReverse p.val.1 p.val.2 hp.1 hp.2 p.property
  have hOldPairInvariant :
      ∀ (h : H) (p : A), p ∈ Sold →
        oldPair (action h p) = oldPair p := by
    intro h p hp
    exact hOldInvariant h p.val.1 p.val.2 hp.1 hp.2 p.property
  have hSafePairs : ∀ p : A, p ∉ Sold →
      (∃ h : H, action h p = tau p) →
      ∃ c : C, d.phi c = f p ∧ d.reverse c = c := by
    intro p hp ⟨h, hswap⟩
    have hswap' := congrArg Subtype.val hswap
    have hx : rho h p.val.1 = p.val.2 :=
      congrArg Prod.fst hswap'
    have hy : rho h p.val.2 = p.val.1 :=
      congrArg Prod.snd hswap'
    exact hSafeNew h p.val.1 p.val.2 p.property hp hx hy
  obtain ⟨edgeColour, hPhi, hRev, hInv, hOld⟩ :=
    exists_groupInvariantRawOrbitColour_extendingSubset
      d action tau (effectiveCrossPairReverse_involutive D)
      hCommute f hInvariant hReverse Sold
      hSoldRev hSoldGroup oldPair hOldPairPhi
      hOldPairRev hOldPairInvariant hSafePairs
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
