import SemigenericEPPA.Algebra.CoherentPaddingSize
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Embedding

/-!
# Fix one old embedding in the factorial fibre before later H-actions

For an original finite old carrier A, the padding size
M=|A|! is at least |A|, including the empty case (0!=1).
Thus there is a fixed injection
    j : A ↪ Fin M.
The same j can be used in every E-class's original embedding;
all later S⊆A and all H-actions use its restriction.

The important quantifier order is ∃j, THEN ∀S,∀H.
No S-dependent choice of original embedding is made.
-/

namespace SemigenericEPPA

universe u

/-- An explicit fixed old injection into the global factorial
padded fibre, chosen solely from the original finite carrier. -/
theorem exists_fixedFactorialOldInjection
    (A : Type u) [Fintype A] :
    ∃ j : A → Fin (coherentPaddingSize A),
      Function.Injective j := by
  classical
  have hsize : Fintype.card A ≤ coherentPaddingSize A :=
    Nat.self_le_factorial (Fintype.card A)
  let j : A ↪ Fin (coherentPaddingSize A) :=
    (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb hsize)
  exact ⟨j, j.injective⟩

end SemigenericEPPA
