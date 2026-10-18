import SemigenericEPPA.Bridge.InvariantRawGroupOrbits
import SemigenericEPPA.Structure.RawCoverFixedGroupLift
import Mathlib.Data.Fintype.Prod

/-!
# Safe group actions on the actual directed cross-pairs of an effective geometry

The invariant-orbit raw-colouring theorem works on an abstract finite
H-set with a commuting reversal. Here that set is concretely

  {(x,y) : V × V // ¬ E(x,y)}

for a genuine effective rectangle geometry D.

An H-action by effective automorphisms induces a homomorphic action on
these ordered cross-pairs. Reversal exchanges their coordinates and
commutes with the action. A pair is reversed by an H-element precisely
when that element exchanges BOTH endpoints. The paper's safety
hypothesis therefore supplies exactly the fixed-orbit condition in
the abstract orbit-colouring theorem.

We prove existence of a raw colour on EVERY ordered cross-pair
which projects to F, respects reversal, and is invariant under H.
Same-part dummy pairs can have any fixed default raw colour.

This theorem is a genuine geometric bridge toward the fixed-cover
homomorphic raw-lift lemma. It does not yet assert coherent EPPA.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w} {V : Type t}
variable {d : RawDatum G C}

/-- Exactly the finite set of ordered pairs of distinct E-parts.
Same-part dummy effective F-values are deliberately excluded. -/
abbrev EffectiveCrossPair (D : EffectiveGeometry d.s V) :=
  {p : V × V // ¬D.part p.1 p.2}

/-- The precise reversal involution on the directed cross-pair set. -/
def effectiveCrossPairReverse
    (D : EffectiveGeometry d.s V) :
    EffectiveCrossPair D → EffectiveCrossPair D :=
  fun p => ⟨(p.val.2, p.val.1), by
    intro h
    exact p.property (D.part.iseqv.symm h)⟩

theorem effectiveCrossPairReverse_involutive
    (D : EffectiveGeometry d.s V) :
    Function.Involutive (effectiveCrossPairReverse D) := by
  intro p
  apply Subtype.ext
  rfl

/-- Every effective automorphism permutes the genuine directed
cross-pairs, with the inverse induced by the inverse group element. -/
def effectiveCrossPairPerm
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y : V,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (h : H) : Equiv.Perm (EffectiveCrossPair D) where
  toFun := fun p => ⟨(rho h p.val.1, rho h p.val.2), by
    intro hxy
    exact p.property ((hE h p.val.1 p.val.2).mp hxy)⟩
  invFun := fun p => ⟨(rho h⁻¹ p.val.1, rho h⁻¹ p.val.2), by
    intro hxy
    exact p.property ((hE h⁻¹ p.val.1 p.val.2).mp hxy)⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · change rho h⁻¹ (rho h p.val.1) = p.val.1
      rw [map_inv]
      exact (rho h).symm_apply_apply p.val.1
    · change rho h⁻¹ (rho h p.val.2) = p.val.2
      rw [map_inv]
      exact (rho h).symm_apply_apply p.val.2
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · change rho h (rho h⁻¹ p.val.1) = p.val.1
      rw [map_inv]
      exact (rho h).apply_symm_apply p.val.1
    · change rho h (rho h⁻¹ p.val.2) = p.val.2
      rw [map_inv]
      exact (rho h).apply_symm_apply p.val.2

/-- A homomorphism on vertices induces a homomorphism on the exact
directed cross-pair subtype, with no equality of within-part dummy
colours assumed. -/
def effectiveCrossPairAction
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y : V,
      D.part (rho h x) (rho h y) ↔ D.part x y) :
    H →* Equiv.Perm (EffectiveCrossPair D) where
  toFun := effectiveCrossPairPerm D rho hE
  map_one' := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    apply Prod.ext
    · change rho 1 p.val.1 = p.val.1
      rw [map_one]
      rfl
    · change rho 1 p.val.2 = p.val.2
      rw [map_one]
      rfl
  map_mul' := by
    intro h k
    apply Equiv.ext
    intro p
    apply Subtype.ext
    apply Prod.ext
    · change rho (h * k) p.val.1 =
        rho h (rho k p.val.1)
      rw [map_mul]
      rfl
    · change rho (h * k) p.val.2 =
        rho h (rho k p.val.2)
      rw [map_mul]
      rfl

/-- An effective H-action has one invariant raw-colour choice on
the entire directed cross-pair set whenever every actual H-swap of
two vertices in different E-classes has a self-reversing raw colour.

In particular, the condition refers to an element exchanging both
endpoints, not necessarily an involution of the whole group H.
That distinction is essential for coherent and relative DLF claims. -/
theorem exists_groupInvariantRawCrossColour
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (hSafe : ∀ (h : H) (x y : V),
      ¬D.part x y →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    ∃ colour : V → V → C,
      (∀ x y, ¬D.part x y →
        d.phi (colour x y) = D.F x y) ∧
      (∀ x y, ¬D.part x y →
        colour y x = d.reverse (colour x y)) ∧
      (∀ h : H, ∀ x y, ¬D.part x y →
        colour (rho h x) (rho h y) = colour x y) := by
  classical
  let A := EffectiveCrossPair D
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype A := inferInstance
  let action : H →* Equiv.Perm A :=
    effectiveCrossPairAction D rho hE
  let tau : A → A := effectiveCrossPairReverse D
  let f : A → G := fun p => D.F p.val.1 p.val.2
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
  have hSafePair : ∀ p : A,
      (∃ h : H, action h p = tau p) →
      ∃ c : C, d.phi c = f p ∧ d.reverse c = c := by
    intro p ⟨h, hp⟩
    have hp' := congrArg Subtype.val hp
    have hx : rho h p.val.1 = p.val.2 :=
      congrArg Prod.fst hp'
    have hy : rho h p.val.2 = p.val.1 :=
      congrArg Prod.snd hp'
    exact hSafe h p.val.1 p.val.2 p.property hx hy
  obtain ⟨edgeColour, hPhi, hRev, hInv⟩ :=
    exists_groupInvariantRawOrbitColour
      d action tau (effectiveCrossPairReverse_involutive D)
      hCommute f hInvariant hReverse hSafePair
  let default : C := Classical.choose (d.phi_surjective 1)
  let colour : V → V → C := fun x y =>
    if hxy : ¬D.part x y then
      edgeColour ⟨(x,y), hxy⟩ else default
  have hc (x y : V) (hxy : ¬D.part x y) :
      colour x y = edgeColour ⟨(x,y), hxy⟩ := by
    simp [colour, hxy]
  refine ⟨colour, ?_, ?_, ?_⟩
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
    have h := hInv h ⟨(x,y),hxy⟩
    change edgeColour ⟨(rho h x,rho h y),hxy'⟩ =
      edgeColour ⟨(x,y),hxy⟩ at h
    rw [hc (rho h x) (rho h y) hxy', hc x y hxy]
    exact h

end SemigenericEPPA
