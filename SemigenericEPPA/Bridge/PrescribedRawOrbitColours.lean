import SemigenericEPPA.Bridge.InvariantRawOrbitColours

/-!
# Extension of prescribed old raw colours on reversible orbit sets

In the fixed-cover homomorphic raw lift, a finite group acts on an
effective witness but the chosen invariant raw colouring must agree
with the ORIGINAL raw colours on the old induced substructure D.

After factoring through the group orbit quotient Q, those old
prescriptions are a partial raw colouring on a subset S of Q stable
under ordered-edge reversal. On S the raw colours already lift the
effective colours and reverse correctly.

The only additional condition needed to extend them to all of Q
is the existence of a self-reversing raw colour in every new
reversal-fixed orbit outside S. Apply the previously certified
unprescribed orbit-colouring result globally (old fixed orbits are
safe because of the prescribed old colours), and replace its values
on S by the prescribed ones.

The resulting complete raw colouring agrees with all old colours
LITERALLY and is reversal-equivariant everywhere. This is the
prescribed-edges part of the manuscript's fixed-cover group raw lift.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {Q : Type w}

/-- Exact extension of a reversal-compatible raw colouring already
prescribed on a reversal-stable finite subset S. No injectivity of
the raw fibre map or fixed-point choice outside its own fibre is
assumed. -/
theorem exists_finiteRawColour_extending_involutiveSubset
    [Finite Q]
    (d : RawDatum G C)
    (tau : Q → Q) (htau : Function.Involutive tau)
    (f : Q → G)
    (hf : ∀ q, f (tau q) = d.s (f q))
    (S : Set Q)
    (hS : ∀ q, q ∈ S ↔ tau q ∈ S)
    (old : Q → C)
    (hOldPhi : ∀ q, q ∈ S → d.phi (old q) = f q)
    (hOldReverse : ∀ q, q ∈ S →
      old (tau q) = d.reverse (old q))
    (hFixedNew : ∀ q, q ∉ S → tau q = q →
      ∃ c : C, d.phi c = f q ∧ d.reverse c = c) :
    ∃ colour : Q → C,
      (∀ q, d.phi (colour q) = f q) ∧
      (∀ q, colour (tau q) = d.reverse (colour q)) ∧
      (∀ q, q ∈ S → colour q = old q) := by
  classical
  have hFixedAll : ∀ q, tau q = q →
      ∃ c : C, d.phi c = f q ∧ d.reverse c = c := by
    intro q hq
    by_cases hqS : q ∈ S
    · refine ⟨old q, hOldPhi q hqS, ?_⟩
      have h := hOldReverse q hqS
      rw [hq] at h
      exact h.symm
    · exact hFixedNew q hqS hq
  obtain ⟨base, hBasePhi, hBaseReverse⟩ :=
    exists_finiteRawColour_of_involutiveOrbits
      d tau htau f hf hFixedAll
  let colour : Q → C := fun q =>
    if q ∈ S then old q else base q
  refine ⟨colour, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q ∈ S
    · have hc : colour q = old q := by
        simp [colour, hq]
      rw [hc]
      exact hOldPhi q hq
    · have hc : colour q = base q := by
        simp [colour, hq]
      rw [hc]
      exact hBasePhi q
  · intro q
    by_cases hq : q ∈ S
    · have hq' : tau q ∈ S := (hS q).mp hq
      change (if tau q ∈ S then old (tau q)
        else base (tau q)) =
        d.reverse (if q ∈ S then old q else base q)
      rw [if_pos hq', if_pos hq]
      exact hOldReverse q hq
    · have hq' : tau q ∉ S := by
        intro ht
        exact hq ((hS q).mpr ht)
      change (if tau q ∈ S then old (tau q)
        else base (tau q)) =
        d.reverse (if q ∈ S then old q else base q)
      rw [if_neg hq', if_neg hq]
      exact hBaseReverse q
  · intro q hq
    simp [colour, hq]

end SemigenericEPPA
