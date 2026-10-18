import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card

/-!
# A single divisible padding size for every later induced substructure

For the positive coherent-EPPA construction (manuscript §4),
the finite witness must be chosen BEFORE the induced old substructure
D and its finite automorphism group H are selected.

It is insufficient to pad each part merely to the original size:
the H-action on the occupied part needs a product presentation
  U_i ≃ (D ∩ A_i) × Fin (M / |D ∩ A_i|).
The same M must therefore be divisible by every nonzero part size
arising from ANY later induced D⊆A.

A simple uniform choice is M=|A|!. It is chosen solely from the
original finite carrier A; every nonempty subset S⊆A has
|S| ∣ M and hence admits a positive integer multiplicity.
This avoids separate choices of least common multiples and makes
the quantifier order explicit.

The following are cardinality/size gates, not an H-equivariant
padding action, a full effective group lift or coherent EPPA.
-/

namespace SemigenericEPPA

universe u

/-- One witness padding size, fixed before choosing an induced
substructure or group action. -/
def coherentPaddingSize (A : Type u) [Fintype A] : ℕ :=
  (Fintype.card A).factorial

/-- Every nonempty subset cardinality divides the SAME global size. -/
theorem coherentPaddingSize_card_dvd
    {A : Type u} [Fintype A] (S : Finset A) (hS : S.Nonempty) :
    S.card ∣ coherentPaddingSize A := by
  unfold coherentPaddingSize
  have hpositive : 0 < S.card := Finset.card_pos.mpr hS
  have hsmall : S.card ≤ Fintype.card A := by
    simpa using (Finset.card_le_univ S)
  exact Nat.dvd_factorial hpositive hsmall

/-- A multiplicity factor for padding any chosen nonempty old fibre
to the global size. Crucially, this factor is chosen AFTER the
size M has already been fixed independently of S. -/
theorem exists_coherentPaddingMultiplicity
    {A : Type u} [Fintype A] (S : Finset A) (hS : S.Nonempty) :
    ∃ t : ℕ, S.card * t = coherentPaddingSize A := by
  obtain ⟨t, ht⟩ := coherentPaddingSize_card_dvd S hS
  exact ⟨t, ht.symm⟩

/-- The uniform coherent padding has positive size as soon as the
original carrier is finite; the empty-carrier case is covered by 0!=1. -/
theorem coherentPaddingSize_pos
    (A : Type u) [Fintype A] :
    0 < coherentPaddingSize A := by
  unfold coherentPaddingSize
  exact Nat.factorial_pos _

end SemigenericEPPA
