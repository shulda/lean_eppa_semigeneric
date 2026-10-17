import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Logic.Equiv.Fintype

/-!
# Extending the partial E-class map to a permutation

An old partial isomorphism is defined only on a subset S of the real
vertices.  The induced map on the E-classes *met by S* is injective,
although the vertex map on S need not be a map of entire E-classes.

We quotient S by the restricted equivalence, embed this finite
quotient twice into V/E (before and after the partial map), and extend
these two injections to a permutation of all of V/E. This is the
first permutation gate of the effective EPPA construction (3.16)--(3.19).
It uses no equal-size assumption on the individual E-classes and no
partial-automorphism extension theorem.
-/

namespace SemigenericEPPA

universe u v

variable {V : Type u}

/-- The equivalence on a partial domain induced by the ambient E relation. -/
private def restrictedPartSetoid (E : Setoid V) (S : Set V) : Setoid S where
  r x y := E x.val y.val
  iseqv := by
    constructor
    · intro x
      exact E.iseqv.refl x.val
    · intro x y hxy
      exact E.iseqv.symm hxy
    · intro x y z hxy hyz
      exact E.iseqv.trans hxy hyz

/-- Every finite partial map which preserves and reflects E induces a
partial injection between E-classes, extending to a global permutation
of the imaginary sort V/E. The domain S can be empty or meet only part
of an E-class; no uniformity of class sizes is assumed. -/
theorem exists_partPermutation_extending
    [Finite V] (E : Setoid V) (S : Set V) (p : S → V)
    (hE : ∀ x y : S, E x.val y.val ↔ E (p x) (p y)) :
    ∃ ι : Equiv.Perm (Quotient E),
      ∀ x : S, ι (Quotient.mk E x.val) = Quotient.mk E (p x) := by
  classical
  let R : Setoid S := restrictedPartSetoid E S
  let f : Quotient R → Quotient E :=
    Quotient.lift (fun x : S => Quotient.mk E x.val) (by
      intro x y hxy
      exact Quotient.sound hxy)
  let g : Quotient R → Quotient E :=
    Quotient.lift (fun x : S => Quotient.mk E (p x)) (by
      intro x y hxy
      exact Quotient.sound ((hE x y).mp hxy))
  have hf : Function.Injective f := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        change E x.val y.val
        exact Quotient.exact
          (show Quotient.mk E x.val = Quotient.mk E y.val from hab)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        exact (hE x y).mpr (Quotient.exact hab)
  letI : Finite (Quotient R) := inferInstance
  obtain ⟨ι, hι⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨ι, ?_⟩
  intro x
  have hx := hι (Quotient.mk R x)
  change ι (Quotient.mk E x.val) = Quotient.mk E (p x) at hx
  exact hx

variable {G : Type v} [Group G] {s : AffineAntiInvolution G}

/-- The exact E-part permutation required for the effective
semigeneric valuation witness, under only E preservation/reflection
on the old partial domain. This does not yet construct a compatible
real-label permutation or the twists and multipliers. -/
theorem EffectiveGeometry.exists_partPermutation_extending
    [Finite V] (D : EffectiveGeometry s V)
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y)) :
    ∃ ι : Equiv.Perm (Quotient D.part),
      ∀ x : S,
        ι (Quotient.mk D.part x.val) = Quotient.mk D.part (p x) :=
  _root_.SemigenericEPPA.exists_partPermutation_extending D.part S p hE

end SemigenericEPPA
