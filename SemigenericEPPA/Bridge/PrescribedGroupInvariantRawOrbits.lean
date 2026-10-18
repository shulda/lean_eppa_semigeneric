import SemigenericEPPA.Bridge.InvariantRawGroupOrbits

/-!
# H-invariant raw-colour selection extending prescribed old orbits

For the positive coherent and relative DLF constructions, raw colours
on the old induced substructure cannot be chosen anew. An H-action
on directed cross-pairs has a reversal- and H-stable collection S of
old pairs on which colours are already prescribed. Those colours
project to the effective colour, reverse correctly, and are
H-invariant on S.

Outside S only, require the usual safety condition: whenever an
H-element reverses a pair, its effective fibre has a self-reversing
raw colour. On a reversed orbit meeting S the condition follows
automatically from invariance and reversal of the prescribed data.

Apply the existing abstract H-orbit selection theorem globally and
replace its colours on S by the prescribed colours. Stability of S
ensures reversal-equivariance and H-invariance remain true.
No quotient-type choices or group finiteness hypotheses are added.
-/

namespace SemigenericEPPA

universe u v w t
variable {H : Type u} [Group H]
variable {A : Type v}
variable {G : Type w} [Group G] {C : Type t}

/-- Extend H-invariant prescribed raw colours on an H- and
reversal-stable subset of a finite directed-edge H-set. The
self-reversing raw-fibre condition is needed ONLY for reversal
orbits entirely outside the old subset. -/
theorem exists_groupInvariantRawOrbitColour_extendingSubset
    [Finite A]
    (d : RawDatum G C)
    (rho : H →* Equiv.Perm A)
    (tau : A → A) (htau : Function.Involutive tau)
    (htauCommute : ∀ (h : H) (a : A),
      tau (rho h a) = rho h (tau a))
    (f : A → G)
    (hfInvariant : ∀ (h : H) (a : A), f (rho h a) = f a)
    (hfReverse : ∀ a, f (tau a) = d.s (f a))
    (S : Set A)
    (hSrev : ∀ a, a ∈ S ↔ tau a ∈ S)
    (hSgroup : ∀ (h : H) (a : A), a ∈ S ↔ rho h a ∈ S)
    (old : A → C)
    (hOldPhi : ∀ a, a ∈ S → d.phi (old a) = f a)
    (hOldReverse : ∀ a, a ∈ S →
      old (tau a) = d.reverse (old a))
    (hOldInvariant : ∀ (h : H) (a : A), a ∈ S →
      old (rho h a) = old a)
    (hSafeNew : ∀ a, a ∉ S →
      (∃ h : H, rho h a = tau a) →
      ∃ c : C, d.phi c = f a ∧ d.reverse c = c) :
    ∃ colour : A → C,
      (∀ a, d.phi (colour a) = f a) ∧
      (∀ a, colour (tau a) = d.reverse (colour a)) ∧
      (∀ (h : H) (a : A), colour (rho h a) = colour a) ∧
      (∀ a, a ∈ S → colour a = old a) := by
  classical
  have hSafe : ∀ a, (∃ h : H, rho h a = tau a) →
      ∃ c : C, d.phi c = f a ∧ d.reverse c = c := by
    intro a hswap
    by_cases ha : a ∈ S
    · obtain ⟨h, hswap'⟩ := hswap
      have hOldSwap : old (tau a) = old a := by
        rw [← hswap']
        exact hOldInvariant h a ha
      refine ⟨old a, hOldPhi a ha, ?_⟩
      calc
        d.reverse (old a) = old (tau a) :=
          (hOldReverse a ha).symm
        _ = old a := hOldSwap
    · exact hSafeNew a ha hswap
  obtain ⟨base, hBasePhi, hBaseReverse, hBaseInvariant⟩ :=
    exists_groupInvariantRawOrbitColour
      d rho tau htau htauCommute f hfInvariant hfReverse hSafe
  let colour : A → C := fun a =>
    if a ∈ S then old a else base a
  refine ⟨colour, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ S
    · change d.phi (if a ∈ S then old a else base a) = f a
      rw [if_pos ha]
      exact hOldPhi a ha
    · change d.phi (if a ∈ S then old a else base a) = f a
      rw [if_neg ha]
      exact hBasePhi a
  · intro a
    by_cases ha : a ∈ S
    · have hta : tau a ∈ S := (hSrev a).mp ha
      change (if tau a ∈ S then old (tau a) else base (tau a)) =
        d.reverse (if a ∈ S then old a else base a)
      rw [if_pos hta, if_pos ha]
      exact hOldReverse a ha
    · have hta : tau a ∉ S := by
        intro ht
        exact ha ((hSrev a).mpr ht)
      change (if tau a ∈ S then old (tau a) else base (tau a)) =
        d.reverse (if a ∈ S then old a else base a)
      rw [if_neg hta, if_neg ha]
      exact hBaseReverse a
  · intro h a
    by_cases ha : a ∈ S
    · have hta : rho h a ∈ S := (hSgroup h a).mp ha
      change (if rho h a ∈ S then old (rho h a)
        else base (rho h a)) =
        (if a ∈ S then old a else base a)
      rw [if_pos hta, if_pos ha]
      exact hOldInvariant h a ha
    · have hta : rho h a ∉ S := by
        intro ht
        exact ha ((hSgroup h a).mpr ht)
      change (if rho h a ∈ S then old (rho h a)
        else base (rho h a)) =
        (if a ∈ S then old a else base a)
      rw [if_neg hta, if_neg ha]
      exact hBaseInvariant h a
  · intro a ha
    change (if a ∈ S then old a else base a) = old a
    rw [if_pos ha]

end SemigenericEPPA
