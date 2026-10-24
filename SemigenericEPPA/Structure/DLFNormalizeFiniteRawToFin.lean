import SemigenericEPPA.Structure.DLFOldPartCloneExtension
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact normalization of an arbitrary finite raw rectangle to Fin n

Any finite original E/R_c raw rectangle has an induced isomorphic
copy on the canonical carrier Fin (card V), obtained by pulling
back along the inverse of a finite-carrier equivalence.

Consequently, an infinite original raw structure containing
induced copies of every RawRectanglePresentation on all Fin n
already contains induced copies of EVERY finite raw presentation
on any finite carrier. This closes the difference between the
canonical age enumeration and the actual original-language age.

This is independent of DLF, good affine congruence orbits,
coherent EPPA and finite SAP.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {W : Type w} {X : Type t}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Every finite original raw R1–R3 presentation has an EXACT
induced embedding into a canonical Fin n raw presentation.
The target is obtained by literal pullback along an equivalence,
not by forgetting the original raw labels. -/
theorem exists_canonicalFin_copy
    (P : RawRectanglePresentation d W)
    [Fintype W] :
    ∃ (n : ℕ) (Q : RawRectanglePresentation d (Fin n))
      (e : W → Fin n),
      Function.Injective e ∧
      (∀ x y : W, Q.part (e x) (e y) ↔ P.part x y) ∧
      (∀ x y : W, Q.colour (e x) (e y) = P.colour x y) := by
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let Q : RawRectanglePresentation d (Fin (Fintype.card W)) :=
    P.pullbackRaw e.symm
  refine ⟨Fintype.card W, Q, e, e.injective, ?_, ?_⟩
  · intro x y
    change P.part (e.symm (e x)) (e.symm (e y)) ↔ P.part x y
    simp
  · intro x y
    change P.colour (e.symm (e x)) (e.symm (e y)) = P.colour x y
    simp

/-- Universality for all raw rectangles on Fin n implies full
original-language age universality on arbitrary finite carriers,
including every ordered raw R_c predicate. -/
theorem inducedFiniteAge_of_canonicalFinAge
    (M : RawRectanglePresentation d X)
    (hFin : ∀ (n : ℕ) (Q : RawRectanglePresentation d (Fin n)),
      ∃ f : Fin n → X,
        Function.Injective f ∧
        (∀ x y : Fin n, M.part (f x) (f y) ↔ Q.part x y) ∧
        (∀ x y : Fin n, M.colour (f x) (f y) = Q.colour x y)) :
    ∀ (V : Type w) [Fintype V] (P : RawRectanglePresentation d V),
      ∃ f : V → X,
        Function.Injective f ∧
        (∀ x y : V, M.part (f x) (f y) ↔ P.part x y) ∧
        (∀ x y : V, M.colour (f x) (f y) = P.colour x y) := by
  intro V _ P
  obtain ⟨n, Q, e, he, hp, hc⟩ := P.exists_canonicalFin_copy
  obtain ⟨f, hf, hfp, hfc⟩ := hFin n Q
  refine ⟨f ∘ e, hf.comp he, ?_, ?_⟩
  · intro x y
    exact (hfp (e x) (e y)).trans (hp x y)
  · intro x y
    exact (hfc (e x) (e y)).trans (hc x y)

end RawRectanglePresentation
end SemigenericEPPA
