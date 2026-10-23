import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

/-!
# Orbit-saturating prescribed colours that start on a NONINVARIANT subset

Relative safe EPPA begins with A⊆B and an H-action only on A.
Inside the phase-expanded witness H can move B\\A outside the
distinguished copy of B; consequently the prescribed original
B-coloured pairs form a reversal-invariant, but NOT H-invariant,
subset of all directed cross pairs.

Before using the certified invariant raw-colour orbit theorem,
we must extend their already prescribed colours to the
H-saturation of this subset. The exact and sufficient premise is
the RETURN condition: if an H-translate of an original coloured
point is original again, the two originally prescribed colours
coincide.

The following lemma proves this cleanly for an arbitrary H-set
and a completely arbitrary colour set C. No group action on
C and no assumption that the prescribed subset was invariant!
Finiteness is not needed. The colour on the complement is
arbitrary and constant on its orbits.

The next stage additionally handles reversal, phi, and safe
self-reversing raw colours on unprescribed reversal orbits.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {A : Type v} {C : Type w}

/-- Saturation of an arbitrary original subset by the full H-action. -/
def orbitSaturation
    (rho : H →* Equiv.Perm A) (S : Set A) : Set A :=
  { b | ∃ a : A, a ∈ S ∧ ∃ h : H, rho h a = b }

/-- The prescribed old subset is contained in its orbit saturation. -/
theorem mem_orbitSaturation_of_mem
    (rho : H →* Equiv.Perm A) (S : Set A)
    (a : A) (ha : a ∈ S) :
    a ∈ orbitSaturation rho S := by
  exact ⟨a, ha, 1, by simp⟩

/-- Saturation is invariant under every element of H, even if
the original S is not invariant. -/
theorem orbitSaturation_stable
    (rho : H →* Equiv.Perm A) (S : Set A)
    (h : H) (b : A)
    (hb : b ∈ orbitSaturation rho S) :
    rho h b ∈ orbitSaturation rho S := by
  obtain ⟨a, ha, k, hka⟩ := hb
  refine ⟨a, ha, h * k, ?_⟩
  calc
    rho (h * k) a = rho h (rho k a) := by rw [map_mul]; rfl
    _ = rho h b := congrArg (rho h) hka

/-- Extend all prescribed colours across their H-orbits.
The only consistency requirement concerns ACTUAL returns into
the original subset, not any imaginary global invariance there.

The extended colouring is H-invariant on the ENTIRE ambient set,
and agrees literally with every prescribed old colour. -/
theorem exists_invariantColour_extending_nonInvariantSubset
    [Nonempty C]
    (rho : H →* Equiv.Perm A)
    (S : Set A)
    (old : A → C)
    (hReturn : ∀ (h : H) (a : A),
      a ∈ S → rho h a ∈ S →
      old (rho h a) = old a) :
    ∃ colour : A → C,
      (∀ a : A, a ∈ S → colour a = old a) ∧
      (∀ (h : H) (a : A), colour (rho h a) = colour a) := by
  classical
  let Sat : Set A := orbitSaturation rho S
  let colour : A → C := fun b =>
    if hb : b ∈ Sat then old (Classical.choose hb)
    else Classical.choice (inferInstance : Nonempty C)
  have hS (a : A) (ha : a ∈ S) : a ∈ Sat :=
    mem_orbitSaturation_of_mem rho S a ha
  have hOld (a : A) (ha : a ∈ S) :
      colour a = old a := by
    have hs : a ∈ Sat := hS a ha
    have hspec := Classical.choose_spec hs
    obtain ⟨hchoose, h, heq⟩ := hspec
    have hcol := hReturn h (Classical.choose hs)
      hchoose ha
    rw [heq] at hcol
    simpa only [colour, dif_pos hs] using hcol.symm
  refine ⟨colour, hOld, ?_⟩
  intro h b
  by_cases hb : b ∈ Sat
  · have hb' : rho h b ∈ Sat :=
      orbitSaturation_stable rho S h b hb
    obtain ⟨ha1, k1, hk1⟩ := Classical.choose_spec hb
    obtain ⟨ha2, k2, hk2⟩ := Classical.choose_spec hb'
    have hrep :
        rho (k2⁻¹ * h * k1) (Classical.choose hb) =
          Classical.choose hb' := by
      apply (rho k2).injective
      calc
        rho k2 (rho (k2⁻¹ * h * k1) (Classical.choose hb)) =
          rho (k2 * (k2⁻¹ * h * k1)) (Classical.choose hb) := by
            rw [map_mul]
            rfl
        _ = rho (h * k1) (Classical.choose hb) := by
            have hg : k2 * (k2⁻¹ * h * k1) = h * k1 := by group
            rw [hg]
        _ = rho h (rho k1 (Classical.choose hb)) := by
            rw [map_mul]
            rfl
        _ = rho h b := congrArg (rho h) hk1
        _ = rho k2 (Classical.choose hb') := hk2.symm
    have hcol :
        old (Classical.choose hb') =
          old (Classical.choose hb) :=
      hReturn (k2⁻¹ * h * k1) (Classical.choose hb)
        ha1 ha2 hrep
    simpa only [colour, dif_pos hb', dif_pos hb] using hcol
  · have hb' : rho h b ∉ Sat := by
      intro hmem
      have hinv := orbitSaturation_stable rho S h⁻¹
        (rho h b) hmem
      have heq : rho h⁻¹ (rho h b) = b := by
        calc
          rho h⁻¹ (rho h b) = rho (h⁻¹ * h) b := by
            rw [map_mul]
            rfl
          _ = b := by simp
      exact hb (heq ▸ hinv)
    simp [colour, hb, hb']

end SemigenericEPPA
