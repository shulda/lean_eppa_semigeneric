import SemigenericEPPA.Algebra.CoherentPaddingSize
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Card

/-!
# Strict H-actions on replicated old fibres

Let H act on a set S of genuine old vertices and on their E-class
indices I, with class compatibility. Choose a multiplicity t_i for
each part index, invariant under H. A replicated old vertex is a
dependent pair (x,r) with x∈S and r∈Fin(t_{class(x)}).

The action h·(x,r)=(h·x,r) is a GENUINE group action; the same
multiplicity coordinate is retained, with only dependent typing
transported. This is the key elementary ingredient missing from
naive uniform padding: any flipped pair of replicated vertices
projects equivariantly to a genuine flipped old pair.

One can later identify the replicated fibres in each occupied
E-class with a fixed prechosen Fin(M) fibre, with M divisible by
every possible occupied class size. The present theorem proves
the complete strict-action/cocycle part, not the existence of
those fibre identifications.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {S : Type v} {I : Type w}

/-- A dependent replicated label: old vertex and a multiplicity
coordinate whose type is allowed to depend on its E-class. -/
abbrev ReplicatedFibreLabel
    (cls : S → I) (t : I → ℕ) :=
  Σ x : S, Fin (t (cls x))

/-- Transport an H-action on old vertices to replicated labels.
The class-index action and H-invariant multiplicities guarantee
that the same numeric copy coordinate remains in range. -/
def replicatedFibreLabelMap
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (h : H)
    (z : ReplicatedFibreLabel cls t) :
    ReplicatedFibreLabel cls t :=
  ⟨rho h z.1, ⟨z.2.val, by
    have heq : t (cls (rho h z.1)) = t (cls z.1) := by
      rw [hCls h z.1, ht h (cls z.1)]
    rw [heq]
    exact z.2.isLt⟩⟩

/-- Exact identity, including the dependent multiplicity coordinate. -/
theorem replicatedFibreLabelMap_one
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (z : ReplicatedFibreLabel cls t) :
    replicatedFibreLabelMap rho iota cls hCls t ht 1 z = z := by
  have hfirst : rho (1 : H) z.1 = z.1 := by simp
  apply Sigma.ext hfirst
  exact (Fin.heq_ext_iff (by rw [hfirst])).mpr rfl

/-- Strict multiplication law in the nondependent ambient group H:
no separate choices of extensions or accidental powers are used. -/
theorem replicatedFibreLabelMap_mul
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (k h : H) (z : ReplicatedFibreLabel cls t) :
    replicatedFibreLabelMap rho iota cls hCls t ht (k * h) z =
      replicatedFibreLabelMap rho iota cls hCls t ht k
        (replicatedFibreLabelMap rho iota cls hCls t ht h z) := by
  have hfirst : rho (k * h) z.1 = rho k (rho h z.1) := by
    rw [map_mul]
    rfl
  apply Sigma.ext hfirst
  exact (Fin.heq_ext_iff (by rw [hfirst])).mpr rfl

/-- One homomorphism into permutations of ALL replicated labels,
automatically invertible with inverse given by h⁻¹. -/
noncomputable def replicatedFibreLabelGroupAction
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i) :
    H →* Equiv.Perm (ReplicatedFibreLabel cls t) := by
  let f : H → ReplicatedFibreLabel cls t →
      ReplicatedFibreLabel cls t :=
    replicatedFibreLabelMap rho iota cls hCls t ht
  have hOne (z : ReplicatedFibreLabel cls t) :
      f 1 z = z :=
    replicatedFibreLabelMap_one rho iota cls hCls t ht z
  have hMul (k h : H) (z : ReplicatedFibreLabel cls t) :
      f (k * h) z = f k (f h z) :=
    replicatedFibreLabelMap_mul rho iota cls hCls t ht k h z
  let p (h : H) : Equiv.Perm (ReplicatedFibreLabel cls t) := {
    toFun := f h
    invFun := f h⁻¹
    left_inv := by
      intro z
      have hh := hMul h⁻¹ h z
      simpa [hOne] using hh.symm
    right_inv := by
      intro z
      have hh := hMul h h⁻¹ z
      simpa [hOne] using hh.symm
  }
  exact {
    toFun := p
    map_one' := by
      apply Equiv.ext
      intro z
      exact hOne z
    map_mul' := by
      intro k h
      apply Equiv.ext
      intro z
      exact hMul k h z
  }

/-- The distinguished copy-zero old embedding into replicated labels. -/
def replicatedFibreOldLabel
    (cls : S → I) (t : I → ℕ)
    (hpos : ∀ x : S, 0 < t (cls x))
    (x : S) : ReplicatedFibreLabel cls t :=
  ⟨x, ⟨0, hpos x⟩⟩

/-- The old copy-zero section is strictly H-equivariant.  This
property is what a fixed-fibre identification must respect. -/
theorem replicatedFibreOldLabel_equivariant
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (cls : S → I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (t : I → ℕ)
    (ht : ∀ (h : H) (i : I),
      t (iota h i) = t i)
    (hpos : ∀ x : S, 0 < t (cls x))
    (h : H) (x : S) :
    replicatedFibreLabelGroupAction rho iota cls hCls t ht h
        (replicatedFibreOldLabel cls t hpos x) =
      replicatedFibreOldLabel cls t hpos (rho h x) := by
  have hfirst : rho h x = rho h x := rfl
  apply Sigma.ext hfirst
  exact (Fin.heq_ext_iff (by rw [hfirst])).mpr rfl

end SemigenericEPPA
