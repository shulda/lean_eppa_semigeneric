import SemigenericEPPA.Algebra.EquivariantFibreMultiplicity
import SemigenericEPPA.Algebra.CoherentPaddingSize
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Factorial.Basic

/-!
# One factorial padding size for every possible later H-invariant fibre

Fix a finite original carrier A and put M=|A|! ONCE.
For any later finite selected carrier S with an injective map S→A,
any class-index map cls:S→I, and any compatible H-action on S and I:

* Each occupied old class fibre X_i has cardinal 0 < |X_i| ≤ |A|.
* Therefore |X_i| divides M, and the canonical t_i=M/|X_i|
  is positive with |X_i|·t_i=M.
* The multiplicity function is literally invariant under H, since
  H transports the actual class fibres by bijections.

This removes both the abstract divisibility and H-invariance
hypotheses from the future replicated fixed-carrier construction.
The witness padding size is chosen BEFORE S, I and H.
-/

namespace SemigenericEPPA

universe u v w z

variable {H : Type u} [Group H]
variable {A : Type v} [Fintype A]
variable {S : Type w} [Fintype S]
variable {I : Type z} [DecidableEq I]

/-- The canonical multiplicity from the original cardinal factorial
satisfies positivity and the exact fibre product equation for every
occupied part, and is strictly H-invariant on all part indices. -/
theorem factorialOldFibreMultiplicity_laws
    (inc : S → A) (hInc : Function.Injective inc)
    (cls : S → I)
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x)) :
    (∀ i : ReplicatedOccupiedIndex cls,
      0 < oldClassFibreMultiplicity cls (coherentPaddingSize A) i.val) ∧
    (∀ i : ReplicatedOccupiedIndex cls,
      Fintype.card (ReplicatedOldFibre cls i) *
        oldClassFibreMultiplicity cls (coherentPaddingSize A) i.val =
          coherentPaddingSize A) ∧
    (∀ (h : H) (i : I),
      oldClassFibreMultiplicity cls (coherentPaddingSize A) (iota h i) =
        oldClassFibreMultiplicity cls (coherentPaddingSize A) i) := by
  classical
  have hpos (i : ReplicatedOccupiedIndex cls) :
      0 < Fintype.card (ReplicatedOldFibre cls i) := by
    obtain ⟨x, hx⟩ := i.property
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  have hdiv (i : ReplicatedOccupiedIndex cls) :
      Fintype.card (ReplicatedOldFibre cls i) ∣
        coherentPaddingSize A := by
    let embedding : ReplicatedOldFibre cls i → A :=
      fun x => inc x.val
    have hEmbedding : Function.Injective embedding :=
      hInc.comp Subtype.val_injective
    have hBound : Fintype.card (ReplicatedOldFibre cls i) ≤
        Fintype.card A :=
      Fintype.card_le_of_injective embedding hEmbedding
    exact Nat.dvd_factorial (hpos i) hBound
  constructor
  · intro i
    change 0 < coherentPaddingSize A /
      Fintype.card (ReplicatedOldFibre cls i)
    exact Nat.div_pos
      (Nat.le_of_dvd (coherentPaddingSize_pos A) (hdiv i))
      (hpos i)
  constructor
  · intro i
    change Fintype.card (ReplicatedOldFibre cls i) *
      (coherentPaddingSize A / Fintype.card (ReplicatedOldFibre cls i)) =
        coherentPaddingSize A
    exact Nat.mul_div_cancel' (hdiv i)
  · intro h i
    exact oldClassFibreMultiplicity_invariant
      rho iota cls hCls (coherentPaddingSize A) h i

end SemigenericEPPA
