import SemigenericEPPA.Algebra.RawDatum
import Mathlib.Order.Basic
import Mathlib.Data.Option.Basic

/-!
# Extending prescribed raw colours over effective cross-part geometry

Suppose E is an equivalence relation and F(x,y) is an effective
group colour for every ordered pair (same-part values are irrelevant).
Any already prescribed raw edges, closed under reversal and mapping
to their proper effective colours, can be extended to a total raw
cross-part colouring.

The construction chooses an orientation of each unordered pair using
an auxiliary linear order and chooses a raw colour in the appropriate
fibre of the surjective map phi. The opposite orientation is given by
raw reversal. This needs NO self-reversing raw colour: distinct
cross-part vertices are never fixed by reversal of ordered pairs.

This lemma handles the raw-surjectivity component of the strong
amalgamation construction; it does NOT establish the effective
rectangle geometry or the full strong-amalgamation theorem.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} [LinearOrder V]

namespace RawDatum

/-- Canonical choice of some raw colour in the requested effective fibre.
There is no algebraic assumption on the fibre sizes. -/
noncomputable def preimage (d : RawDatum G C) (g : G) : C :=
  Classical.choose (d.phi_surjective g)

theorem preimage_spec (d : RawDatum G C) (g : G) :
    d.phi (d.preimage g) = g :=
  Classical.choose_spec (d.phi_surjective g)

/-- Prefer an existing prescribed raw colour; otherwise choose one
from the effective fibre. -/
noncomputable def positiveRaw
    (d : RawDatum G C) (old : V → V → Option C)
    (F : V → V → G) (x y : V) : C :=
  match old x y with
  | some c => c
  | none => d.preimage (F x y)

/-- The positive-orientation choice retains prescribed colours. -/
theorem positiveRaw_of_prescribed
    (d : RawDatum G C) (old : V → V → Option C)
    (F : V → V → G) (x y : V) (c : C)
    (hc : old x y = some c) :
    d.positiveRaw old F x y = c := by
  simp [positiveRaw, hc]

/-- The positive-orientation choice always has the required
effective colour when the prescribed ones do. -/
theorem positiveRaw_phi
    (d : RawDatum G C) (old : V → V → Option C)
    (F : V → V → G)
    (hcompat : ∀ x y c, old x y = some c → d.phi c = F x y)
    (x y : V) :
    d.phi (d.positiveRaw old F x y) = F x y := by
  cases h : old x y with
  | none =>
    simp [positiveRaw, h, preimage_spec]
  | some c =>
    simpa [positiveRaw, h] using hcompat x y c h

/-- The completed raw colouring. Edges inside E-parts are left blank;
for distinct E-parts we use the prescribed colour when present and
otherwise choose a fibre colour, canonically orienting each unordered
pair according to the auxiliary order. -/
noncomputable def completeRaw
    (d : RawDatum G C) (E : V → V → Prop)
    (old : V → V → Option C) (F : V → V → G) :
    V → V → Option C := by
  classical
  exact fun x y =>
    if E x y then none
    else if x < y then some (d.positiveRaw old F x y)
    else some (d.reverse (d.positiveRaw old F y x))

/-- There are no raw edges inside E-parts. -/
theorem completeRaw_same
    (d : RawDatum G C) (E : V → V → Prop)
    (old : V → V → Option C) (F : V → V → G)
    (x y : V) (hxy : E x y) :
    d.completeRaw E old F x y = none := by
  simp [completeRaw, hxy]

/-- Every ordered cross-part pair has a raw colour. -/
theorem completeRaw_cross
    (d : RawDatum G C) (E : V → V → Prop)
    (old : V → V → Option C) (F : V → V → G)
    (x y : V) (hxy : ¬E x y) :
    ∃ c, d.completeRaw E old F x y = some c := by
  by_cases hlt : x < y
  · exact ⟨d.positiveRaw old F x y, by simp [completeRaw, hxy, hlt]⟩
  · exact ⟨d.reverse (d.positiveRaw old F y x),
      by simp [completeRaw, hxy, hlt]⟩

/-- The completed raw colouring has exact reversal symmetry, including
the case of nontrivial affine reversal of effective colours. -/
theorem completeRaw_reverse
    (d : RawDatum G C) (E : V → V → Prop)
    (hE : Equivalence E)
    (old : V → V → Option C) (F : V → V → G)
    (x y : V) :
    d.completeRaw E old F y x =
      Option.map d.reverse (d.completeRaw E old F x y) := by
  by_cases hpart : E x y
  · have hpart' : E y x := hE.symm hpart
    simp [completeRaw, hpart, hpart']
  · have hpart' : ¬E y x := by
      intro h
      exact hpart (hE.symm h)
    have hne : x ≠ y := by
      intro h
      subst y
      exact hpart (hE.refl x)
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · have hnot : ¬y < x := not_lt_of_ge (le_of_lt hxy)
      simp [completeRaw, hpart, hpart', hxy, hnot]
    · have hnot : ¬x < y := not_lt_of_ge (le_of_lt hyx)
      simp [completeRaw, hpart, hpart', hyx, hnot,
        d.reverse_involutive]

/-- Every previously prescribed raw edge remains unchanged.
The prescription need not be defined on all cross-part pairs. -/
theorem completeRaw_prescribed
    (d : RawDatum G C) (E : V → V → Prop)
    (hE : Equivalence E)
    (old : V → V → Option C) (F : V → V → G)
    (hOldSame : ∀ x y, E x y → old x y = none)
    (hOldReverse : ∀ x y,
      old y x = Option.map d.reverse (old x y))
    (x y : V) (c : C) (hc : old x y = some c) :
    d.completeRaw E old F x y = some c := by
  have hcross : ¬E x y := by
    intro hpart
    have hnone := hOldSame x y hpart
    rw [hc] at hnone
    cases hnone
  by_cases hxy : x < y
  · simp [completeRaw, hcross, hxy, positiveRaw, hc]
  · have hne : x ≠ y := by
      intro heq
      subst y
      exact hcross (hE.refl x)
    have hyx : y < x := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hxy h).elim
      · exact h
    have hrev : old y x = some (d.reverse c) := by
      rw [hOldReverse x y, hc]
      rfl
    simp [completeRaw, hcross, hxy, hrev, positiveRaw,
      d.reverse_involutive]

/-- Every completed cross-part raw colour projects to the specified
effective colour F. This is independent of fibre cardinalities. -/
theorem completeRaw_phi
    (d : RawDatum G C) (E : V → V → Prop)
    (hE : Equivalence E)
    (old : V → V → Option C) (F : V → V → G)
    (hcompat : ∀ x y c, old x y = some c → d.phi c = F x y)
    (hFreversal : ∀ x y, ¬E x y → F y x = d.s (F x y))
    (x y : V) (hcross : ¬E x y) (c : C)
    (hc : d.completeRaw E old F x y = some c) :
    d.phi c = F x y := by
  by_cases hxy : x < y
  · have hpos := d.positiveRaw_phi old F hcompat x y
    have heq : d.positiveRaw old F x y = c := by
      simpa [completeRaw, hcross, hxy] using hc
    rw [← heq]
    exact hpos
  · have hne : x ≠ y := by
      intro heq
      subst y
      exact hcross (hE.refl x)
    have hyx : y < x := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact (hxy h).elim
      · exact h
    have hpos := d.positiveRaw_phi old F hcompat y x
    have heq : d.reverse (d.positiveRaw old F y x) = c := by
      simpa [completeRaw, hcross, hxy] using hc
    rw [← heq, d.equivariant, hpos, hFreversal x y hcross,
      d.s.involutive]

end RawDatum
end SemigenericEPPA
