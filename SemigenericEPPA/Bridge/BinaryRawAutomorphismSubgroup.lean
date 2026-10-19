import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.End

/-!
# Automorphisms preserving a family of literal binary predicates

For coherent EPPA it is not sufficient to produce unrelated
permutations of a raw-cover carrier: every chosen connector and
every group action must preserve E and each individual raw P_c.
These automorphisms form a subgroup of Perm(W).

The elementary subgroup closure and group-lift construction are
proved here once, for ANY carrier, ANY binary equivalence predicate
E (equivalence is not needed), and ANY family of binary predicates
R_c. This gives a genuine group in which conjugation and groupoid
composition can be performed without repeatedly reproving literal
relational preservation.

The result makes NO claim that an arbitrary permutation belongs to
this subgroup; membership must be certified using the raw-cover
individual and homomorphic extension theorems.
-/

namespace SemigenericEPPA

universe u v t

variable {W : Type u} {C : Type v} {H : Type t} [Group H]

/-- Preservation and reflection of a distinguished binary relation
and every indexed ordered binary raw relation on a carrier W. -/
def PreservesBinaryRawRelations
    (E : W → W → Prop) (R : C → W → W → Prop)
    (f : Equiv.Perm W) : Prop :=
  (∀ x y : W, E (f x) (f y) ↔ E x y) ∧
  (∀ c : C, ∀ x y : W, R c (f x) (f y) ↔ R c x y)

/-- The identity preserves the entire literal binary language. -/
theorem preservesBinaryRawRelations_one
    (E : W → W → Prop) (R : C → W → W → Prop) :
    PreservesBinaryRawRelations E R (1 : Equiv.Perm W) := by
  constructor
  · intro x y
    exact Iff.rfl
  · intro c x y
    exact Iff.rfl

/-- Closure under composition in the exact permutation convention. -/
theorem preservesBinaryRawRelations_mul
    (E : W → W → Prop) (R : C → W → W → Prop)
    (f g : Equiv.Perm W)
    (hf : PreservesBinaryRawRelations E R f)
    (hg : PreservesBinaryRawRelations E R g) :
    PreservesBinaryRawRelations E R (f * g) := by
  constructor
  · intro x y
    change E (f (g x)) (f (g y)) ↔ E x y
    exact (hf.1 (g x) (g y)).trans (hg.1 x y)
  · intro c x y
    change R c (f (g x)) (f (g y)) ↔ R c x y
    exact (hf.2 c (g x) (g y)).trans (hg.2 c x y)

/-- Preservation and reflection automatically pass to the inverse. -/
theorem preservesBinaryRawRelations_inv
    (E : W → W → Prop) (R : C → W → W → Prop)
    (f : Equiv.Perm W)
    (hf : PreservesBinaryRawRelations E R f) :
    PreservesBinaryRawRelations E R f⁻¹ := by
  constructor
  · intro x y
    change E (f.symm x) (f.symm y) ↔ E x y
    have h := (hf.1 (f.symm x) (f.symm y)).symm
    simpa only [f.apply_symm_apply] using h
  · intro c x y
    change R c (f.symm x) (f.symm y) ↔ R c x y
    have h := (hf.2 c (f.symm x) (f.symm y)).symm
    simpa only [f.apply_symm_apply] using h

/-- The literal E- and raw-colour-preserving whole-witness
permutations are a genuine subgroup, with no extra assumptions. -/
def binaryRawAutSubgroup
    (E : W → W → Prop) (R : C → W → W → Prop) :
    Subgroup (Equiv.Perm W) where
  carrier := {f | PreservesBinaryRawRelations E R f}
  one_mem' := preservesBinaryRawRelations_one E R
  mul_mem' := by
    intro f g hf hg
    exact preservesBinaryRawRelations_mul E R f g hf hg
  inv_mem' := by
    intro f hf
    exact preservesBinaryRawRelations_inv E R f hf

/-- Any family of certified relation-preserving permutations given
homomorphically by H automatically lands in the true automorphism
subgroup, with no loss of the group law. -/
def binaryRawAutHom
    (E : W → W → Prop) (R : C → W → W → Prop)
    (rho : H →* Equiv.Perm W)
    (hRho : ∀ h : H, PreservesBinaryRawRelations E R (rho h)) :
    H →* binaryRawAutSubgroup E R where
  toFun := fun h => ⟨rho h, hRho h⟩
  map_one' := by
    apply Subtype.ext
    exact map_one rho
  map_mul' := by
    intro h k
    apply Subtype.ext
    exact map_mul rho h k

end SemigenericEPPA
