import Mathlib.Data.Set.Defs
import SemigenericEPPA.Algebra.AffineReversal

/-!
# Raw colour data

This is the algebraic input `(G, s, C, *, φ)` from the manuscript.
Finiteness and the existence of a nonempty alphabet will be imposed by
the *theorem inputs*, not encoded as accidental global axioms.
-/

namespace SemigenericEPPA

/-- A reversal-equivariant, surjective refinement of effective group colours. -/
structure RawDatum (G C : Type*) [Group G] where
  s : AffineAntiInvolution G
  reverse : C → C
  reverse_involutive : ∀ c : C, reverse (reverse c) = c
  phi : C → G
  phi_surjective : Function.Surjective phi
  equivariant : ∀ c : C, phi (reverse c) = s (phi c)

namespace RawDatum

variable {G C : Type*} [Group G]

/-- Effective colours admitting a raw colour fixed by reversal. -/
def selfReverseEffective (d : RawDatum G C) : Set G :=
  { g | ∃ c : C, d.phi c = g ∧ d.reverse c = c }

/-- A self-reversing raw colour has an effective colour fixed by s. -/
theorem selfReverse_phi_fixed (d : RawDatum G C) (c : C)
    (hc : d.reverse c = c) : d.s (d.phi c) = d.phi c := by
  calc
    d.s (d.phi c) = d.phi (d.reverse c) := (d.equivariant c).symm
    _ = d.phi c := by rw [hc]

theorem selfReverseEffective_subset_fixed (d : RawDatum G C) {g : G}
    (hg : g ∈ d.selfReverseEffective) : d.s g = g := by
  obtain ⟨c, hc, hfix⟩ := hg
  have h := d.selfReverse_phi_fixed c hfix
  simpa only [hc] using h

end RawDatum
end SemigenericEPPA
