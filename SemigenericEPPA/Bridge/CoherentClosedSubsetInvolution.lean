import SemigenericEPPA.Bridge.CoherentExtensionForcesInvolution

/-!
# Explicit involution forcing for a closed old transposition

In the exact groupoid of upstream PartialIsomorphisms, every closed
old induced subset S has the identity arrow r = reflOn(A,S).
It is a genuine idempotent in the exact source/range composition,
not an identity partial map on all of A.

Every coherent extension sends r to the whole-witness identity.
If an old partial automorphism p maps S bijectively onto itself,
its exact square is the identity on S, and its language component
has square 1, then coherence forces its whole-witness extension
to be a literal involution.

This is the direct groupoid-to-involution mechanism for the
negative coherent-EPPA obstructions in the rectangle class.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {L : Language.{u}} {Γ : Type v} [Group Γ]
variable (act : L.Action Γ)
variable {V : Type w} {W : Type z}
variable {A : Structure L V} {B : Structure L W}
variable {ψ : Structure.Embedding act A B}

/-- The extension of the exact identity arrow on ANY closed old
subset fixes every vertex of the entire witness. -/
theorem coherentExtension_reflOn_fixes_all
    (e : Structure.CoherentExtension act ψ)
    (S : Set V) (hS : A.IsClosed S)
    (x : W) :
    e.extension (Structure.PartialIsomorphism.reflOn A S hS) x = x := by
  let r : Structure.PartialAutomorphism act A :=
    Structure.PartialIsomorphism.reflOn A S hS
  have hrr : Structure.PartialIsomorphism.CoherentTriple r r r := by
    refine ⟨rfl, ?_⟩
    constructor
    · change (1 : Γ) = 1 * 1
      simp
    · refine ⟨rfl, ?_⟩
      intro y hy
      rfl
  exact coherentExtension_idempotent_fixes_all act e r hrr x

/-- An exact partial involution on a closed old set extends to
a genuine involution of the entire finite/infinite witness.
No restriction to its old source remains in the conclusion. -/
theorem coherentExtension_involution_of_squareOnSource
    (e : Structure.CoherentExtension act ψ)
    (p : Structure.PartialAutomorphism act A)
    (S : Set V) (hS : A.IsClosed S)
    (hSource : p.source = S)
    (hTarget : p.target = S)
    (hLang : p.lang * p.lang = 1)
    (hSquare : ∀ x : V, x ∈ S → p (p x) = x)
    (x : W) :
    e.extension p (e.extension p x) = x := by
  let r : Structure.PartialAutomorphism act A :=
    Structure.PartialIsomorphism.reflOn A S hS
  have hrr : Structure.PartialIsomorphism.CoherentTriple r r r := by
    refine ⟨rfl, ?_⟩
    constructor
    · change (1 : Γ) = 1 * 1
      simp
    · refine ⟨rfl, ?_⟩
      intro y hy
      rfl
  have hMatch : p.target = p.source :=
    hTarget.trans hSource.symm
  have hpp : Structure.PartialIsomorphism.CoherentTriple p p r := by
    refine ⟨hMatch, ?_⟩
    constructor
    · change (1 : Γ) = p.lang * p.lang
      exact hLang.symm
    · refine ⟨?_, ?_⟩
      · change S = p.source
        exact hSource.symm
      · intro y hy
        change y = p (p y)
        exact (hSquare y (by
          change y ∈ S at hy
          exact hy)).symm
  exact coherentExtension_partialInvolution act e p r hrr hpp x

end SemigenericEPPA
