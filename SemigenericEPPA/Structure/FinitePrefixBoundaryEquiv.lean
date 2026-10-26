import SemigenericEPPA.Structure.PrefixChainExactBaseMap
import Mathlib.Logic.Equiv.Sum

/-!
# Exact endpoint equivalences for a finite original relational prefix chain

The initial prefix X ⊕ Fin 0 is exactly equivalent to X,
and the last prefix X ⊕ Fin (min m m) is exactly equivalent
to the original X ⊕ Fin m. These carrier equivalences are
compatible with the *specified* chain inclusion.

This finishes the carrier bookkeeping required when the
canonical finite one-point SAP square is pulled back to
the concrete original finite extension rather than just
an abstract isomorphic copy of it.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

/-- The initial prefix has exactly the original vertices. Defining the
equivalence directly avoids a hidden dependent cast from simp. -/
def prefixInitialEquiv (X : Type u) (m : ℕ) :
    PrefixCarrier X m 0 ≃ X where
  toFun
    | Sum.inl x => x
    | Sum.inr i => Fin.elim0 i
  invFun := Sum.inl
  left_inv := by
    intro z
    cases z with
    | inl x => rfl
    | inr i => exact Fin.elim0 i
  right_inv := by
    intro x
    rfl

/-- The final prefix is literally the full original carrier. We use
explicit Fin indices rather than transporting an Equiv through simp. -/
def prefixFinalEquiv (X : Type u) (m : ℕ) :
    PrefixCarrier X m m ≃ X ⊕ Fin m where
  toFun
    | Sum.inl x => Sum.inl x
    | Sum.inr i => Sum.inr ⟨i.val, by simpa using i.isLt⟩
  invFun
    | Sum.inl x => Sum.inl x
    | Sum.inr i => Sum.inr ⟨i.val, by simpa using i.isLt⟩
  left_inv := by
    intro z
    cases z with
    | inl x => rfl
    | inr i =>
        apply congrArg Sum.inr
        apply Fin.ext
        rfl
  right_inv := by
    intro z
    cases z with
    | inl x => rfl
    | inr i =>
        apply congrArg Sum.inr
        apply Fin.ext
        rfl

@[simp] theorem prefixInitialEquiv_inl
    {X : Type u} (m : ℕ) (x : X) :
    prefixInitialEquiv X m (Sum.inl x) = x :=
  rfl

theorem prefixFinalEquiv_toFinal
    {X : Type u} (m : ℕ) (x : PrefixCarrier X m m) :
    prefixFinalEquiv X m x = prefixToFinal m m x := by
  cases x with
  | inl x => rfl
  | inr i =>
      apply congrArg Sum.inr
      apply Fin.ext
      rfl

variable {G : Type v} [Group G] {C : Type u}
variable {d : RawDatum G C}

/-- At the top of the prefix chain, the literal specified
composite old map becomes the original left-summand
inclusion X → X ⊕ Fin m. -/
theorem prefixFinalEquiv_fromZero_old
    {X : Type (max u v)} [Fintype X] {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (hP : IsRectangleStructure d P)
    (x : X) :
    prefixFinalEquiv X m
      ((finitePrefixOnePointChain P hP).fromZero m le_rfl (Sum.inl x)) =
      Sum.inl x := by
  rw [prefixFinalEquiv_toFinal]
  have h := finitePrefix_fromZero_toFinal P hP m le_rfl (Sum.inl x)
  simpa [prefixToFinal] using h

end SemigenericEPPA
