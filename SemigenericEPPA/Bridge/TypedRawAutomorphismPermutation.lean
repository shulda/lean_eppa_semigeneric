import SemigenericEPPA.Bridge.RawTypedEPPA

/-!
# Recover an actual raw-colour-preserving permutation from a typed automorphism

The positive coherent EPPA construction ends in the shared
AllThoseEPPA.Structure.Automorphism API. The negative coherent
obstruction uses a whole-witness involution and an actual swapped
cross-E raw edge. We need to move BACK from an upstream typed
automorphism to its underlying total bijection without forgetting
preservation of any original R1--R3 relation.

This module constructs that permutation directly from the full
PartialEquiv, and recovers literal preservation of E and every
ordered Option-valued raw colour. No effective-only approximation,
new witness, or additional axioms are used.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {W : Type w}
variable {d : RawDatum G C}

/-- Underlying actual vertex permutation of an upstream typed
automorphism of a literal raw rectangle presentation. -/
noncomputable def RawRectanglePresentation.typedAutomorphismPerm
    (Q : RawRectanglePresentation d W)
    (T : Structure.Automorphism (rectangleTrivialAction C) Q.toStructure) :
    Equiv.Perm W where
  toFun := fun x => T x
  invFun := fun x => T.toPartialIsomorphism.toPartialEquiv.symm x
  left_inv := by
    intro x
    exact T.toPartialIsomorphism.toPartialEquiv.left_inv (by
      change x ∈ T.toPartialIsomorphism.source
      rw [T.source_eq_univ]
      trivial)
  right_inv := by
    intro x
    exact T.toPartialIsomorphism.toPartialEquiv.right_inv (by
      change x ∈ T.toPartialIsomorphism.target
      rw [T.target_eq_univ]
      trivial)

@[simp] theorem RawRectanglePresentation.typedAutomorphismPerm_apply
    (Q : RawRectanglePresentation d W)
    (T : Structure.Automorphism (rectangleTrivialAction C) Q.toStructure)
    (x : W) :
    Q.typedAutomorphismPerm T x = T x :=
  rfl

/-- The recovered permutation preserves and reflects literal E. -/
theorem RawRectanglePresentation.typedAutomorphismPerm_part
    (Q : RawRectanglePresentation d W)
    (T : Structure.Automorphism (rectangleTrivialAction C) Q.toStructure)
    (x y : W) :
    Q.part (Q.typedAutomorphismPerm T x)
      (Q.typedAutomorphismPerm T y) ↔ Q.part x y := by
  have hlang : T.lang = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  have hdom : ∀ i : Fin 2,
      (pairTuple x y) i ∈ T.toPartialIsomorphism.source := by
    intro i
    rw [T.source_eq_univ]
    trivial
  have h := T.toPartialIsomorphism.map_rel_iff
    (binarySymbol C none) (pairTuple x y) hdom
  change T.toPartialIsomorphism.lang = (1 : Equiv.Perm (Fin 0)) at hlang
  rw [hlang, Language.Action.onRel_one] at h
  change Q.part (T x) (T y) ↔ Q.part x y at h
  exact h

/-- The recovered permutation preserves EVERY literal ordered
raw colour, including the absence of colour within E. -/
theorem RawRectanglePresentation.typedAutomorphismPerm_colour
    (Q : RawRectanglePresentation d W)
    (T : Structure.Automorphism (rectangleTrivialAction C) Q.toStructure)
    (x y : W) :
    Q.colour (Q.typedAutomorphismPerm T x)
      (Q.typedAutomorphismPerm T y) = Q.colour x y := by
  have hlang : T.lang = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  have hdom : ∀ i : Fin 2,
      (pairTuple x y) i ∈ T.toPartialIsomorphism.source := by
    intro i
    rw [T.source_eq_univ]
    trivial
  cases hc : Q.colour x y with
  | none =>
      have hsrc : Q.part x y :=
        (Q.colour_none_iff x y).mp hc
      have hdst : Q.part (T x) (T y) :=
        (Q.typedAutomorphismPerm_part T x y).mpr hsrc
      exact (Q.colour_none_iff (T x) (T y)).mpr hdst
  | some c =>
      have h := T.toPartialIsomorphism.map_rel_iff
        (binarySymbol C (some c)) (pairTuple x y) hdom
      change T.toPartialIsomorphism.lang = (1 : Equiv.Perm (Fin 0)) at hlang
  rw [hlang, Language.Action.onRel_one] at h
      change Q.colour (T x) (T y) = some c ↔
        Q.colour x y = some c at h
      exact h.mpr hc

end SemigenericEPPA
