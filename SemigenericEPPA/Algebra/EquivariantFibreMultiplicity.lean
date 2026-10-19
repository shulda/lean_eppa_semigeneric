import SemigenericEPPA.Algebra.CoherentPaddingSize
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.End

/-!
# H-invariance of the number of genuine old vertices in each E-part

Given a strict H-action on a selected old vertex type S and a
compatible action on E-part indices I, the equivalence
  S_i ≃ S_(h i),   x ↦ h x
is literal, including an inverse via h⁻¹. Hence occupied part sizes
are constant on H-orbits, and the canonical multiplicity
  t_i = M / |S_i|
is H-invariant for ONE predetermined padding size M.

This is the cardinality bridge between the fixed factorial fibre
coding and the strict dependent replicated-label action. No choices
of group-element-specific multiplicities are permitted.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {S : Type v} {I : Type w}

/-- Genuine old vertices in the selected E-part i. -/
abbrev OldClassFibre (cls : S → I) (i : I) :=
  {x : S // cls x = i}

/-- The strict H-equivariant bijection between genuine occupied
class fibres, even when i and h i are different index types. -/
def oldClassFibreEquiv
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (h : H) (i : I) :
    OldClassFibre cls i ≃ OldClassFibre cls (iota h i) where
  toFun := fun x => ⟨rho h x.val, by
    rw [hCls h x.val, x.property]⟩
  invFun := fun y => ⟨rho h⁻¹ y.val, by
    calc
      cls (rho h⁻¹ y.val) = iota h⁻¹ (cls y.val) :=
        hCls h⁻¹ y.val
      _ = iota h⁻¹ (iota h i) :=
        congrArg (iota h⁻¹) y.property
      _ = i := by simp⟩
  left_inv := by
    intro x
    apply Subtype.ext
    change rho h⁻¹ (rho h x.val) = x.val
    simp
  right_inv := by
    intro y
    apply Subtype.ext
    change rho h (rho h⁻¹ y.val) = y.val
    simp

/-- A choice-free numeric cardinal of a finite selected E-fibre. -/
noncomputable def oldClassFibreCard
    [Fintype S] (cls : S → I) (i : I) : ℕ := by
  classical
  exact Fintype.card (OldClassFibre cls i)

/-- The old E-class cardinal is constant along every H-orbit on I. -/
theorem oldClassFibreCard_invariant
    [Fintype S]
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (h : H) (i : I) :
    oldClassFibreCard cls (iota h i) =
      oldClassFibreCard cls i := by
  classical
  unfold oldClassFibreCard
  exact Fintype.card_congr
    (oldClassFibreEquiv rho iota cls hCls h i).symm

/-- Canonical orbit-invariant multiplicity, using one prechosen M
independent of the later subset S and group H. On empty fibres it
takes the harmless dummy value 0 and is never used as a replica
coordinate there. -/
noncomputable def oldClassFibreMultiplicity
    [Fintype S] (cls : S → I) (M : ℕ) (i : I) : ℕ :=
  M / oldClassFibreCard cls i

theorem oldClassFibreMultiplicity_invariant
    [Fintype S]
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (M : ℕ) (h : H) (i : I) :
    oldClassFibreMultiplicity cls M (iota h i) =
      oldClassFibreMultiplicity cls M i := by
  unfold oldClassFibreMultiplicity
  rw [oldClassFibreCard_invariant rho iota cls hCls h i]

end SemigenericEPPA
