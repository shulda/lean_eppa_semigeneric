import SemigenericEPPA.Algebra.RawDatum
import Mathlib.Data.Fintype.EquivFin

/-!
# Reversal-compatible raw colouring on an involutive orbit space

Let Q be a finite set of orbits of ordered cross-part edges under
a prescribed finite group action. Reversing an ordered edge induces
an involution tau on Q, and each orbit has a well-defined effective
group colour f(q) with f(tau q)=s(f(q)).

To choose an invariant original raw colour on each orbit, it is
enough to ensure that every fixed point of tau belongs to an
effective fibre containing a self-reversing raw colour. For
nonfixed two-orbits, choose any raw representative on one side
and its reversal on the other.

The following abstract theorem formalizes exactly that selection
step, without identifying opposite fibres or assuming s(1)=1.
It is independent of the raw-cover valuation construction and
will be applied to the quotient of ordered cross-part pairs by
a group action in the fixed-cover homomorphic lift.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {Q : Type w}

/-- A reversible orbit-indexed effective colouring admits a
literal compatible raw lift whenever each fixed orbit has a
self-reversing raw colour in its effective fibre. An auxiliary
order chooses representatives from nonfixed reversal pairs. -/
theorem exists_rawColour_of_involutiveOrbits
    [LinearOrder Q]
    (d : RawDatum G C)
    (tau : Q → Q) (htau : Function.Involutive tau)
    (f : Q → G)
    (hf : ∀ q, f (tau q) = d.s (f q))
    (hfixed : ∀ q, tau q = q →
      ∃ c : C, d.phi c = f q ∧ d.reverse c = c) :
    ∃ colour : Q → C,
      (∀ q, d.phi (colour q) = f q) ∧
      (∀ q, colour (tau q) = d.reverse (colour q)) := by
  classical
  let pick : Q → C := fun q => Classical.choose (d.phi_surjective (f q))
  have hpick (q : Q) : d.phi (pick q) = f q :=
    Classical.choose_spec (d.phi_surjective (f q))
  let colour : Q → C := fun q =>
    if hq : tau q = q then Classical.choose (hfixed q hq)
    else if q < tau q then pick q else d.reverse (pick (tau q))
  have hphi (q : Q) : d.phi (colour q) = f q := by
    by_cases hq : tau q = q
    · have hcol : colour q = Classical.choose (hfixed q hq) := by
        simp [colour, hq]
      rw [hcol]
      exact (Classical.choose_spec (hfixed q hq)).1
    · by_cases hlt : q < tau q
      · have hcol : colour q = pick q := by
          simp [colour, hq, hlt]
        rw [hcol]
        exact hpick q
      · have hcol : colour q = d.reverse (pick (tau q)) := by
          simp [colour, hq, hlt]
        rw [hcol]
        calc
          d.phi (d.reverse (pick (tau q))) =
            d.s (d.phi (pick (tau q))) := d.equivariant _
          _ = d.s (f (tau q)) := congrArg d.s (hpick (tau q))
          _ = d.s (d.s (f q)) := congrArg d.s (hf q)
          _ = f q := d.s.involutive (f q)
  have hreverse (q : Q) :
      colour (tau q) = d.reverse (colour q) := by
    by_cases hq : tau q = q
    · rw [hq]
      have hcol : colour q = Classical.choose (hfixed q hq) := by
        simp [colour, hq]
      rw [hcol]
      exact (Classical.choose_spec (hfixed q hq)).2.symm
    · have hneq : q ≠ tau q := Ne.symm hq
      have hq' : tau (tau q) ≠ tau q := by
        rw [htau q]
        exact hneq
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · have hnlt : ¬tau q < q :=
          not_lt_of_ge (le_of_lt hlt)
        have hcol : colour q = pick q := by
          simp [colour, hq, hlt]
        have hcol' : colour (tau q) = d.reverse (pick q) := by
          simp [colour, hq', htau q, hneq, hnlt]
        rw [hcol, hcol']
      · have hnlt : ¬q < tau q :=
          not_lt_of_ge (le_of_lt hgt)
        have hcol : colour q = d.reverse (pick (tau q)) := by
          simp [colour, hq, hnlt]
        have hcol' : colour (tau q) = pick (tau q) := by
          simp [colour, hq', htau q, hneq, hgt]
        rw [hcol, hcol', d.reverse_involutive]
  exact ⟨colour, hphi, hreverse⟩

/-- Finite orbit sets need no pre-existing linear order.
The auxiliary order is chosen and eliminated internally. -/
theorem exists_finiteRawColour_of_involutiveOrbits
    [Finite Q]
    (d : RawDatum G C)
    (tau : Q → Q) (htau : Function.Involutive tau)
    (f : Q → G)
    (hf : ∀ q, f (tau q) = d.s (f q))
    (hfixed : ∀ q, tau q = q →
      ∃ c : C, d.phi c = f q ∧ d.reverse c = c) :
    ∃ colour : Q → C,
      (∀ q, d.phi (colour q) = f q) ∧
      (∀ q, colour (tau q) = d.reverse (colour q)) := by
  classical
  letI : Fintype Q := Fintype.ofFinite _
  letI : LinearOrder Q :=
    LinearOrder.lift' (Fintype.equivFin Q)
      (Fintype.equivFin Q).injective
  exact exists_rawColour_of_involutiveOrbits
    d tau htau f hf hfixed

end SemigenericEPPA
