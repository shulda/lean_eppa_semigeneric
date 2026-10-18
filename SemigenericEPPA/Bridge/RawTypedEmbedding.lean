import SemigenericEPPA.Structure.RawPresentation
import AllThoseEPPA.Map

/-!
# Literal raw embeddings in the general AllThoseEPPA API

Our finite raw EPPA theorem explicitly supplies an injective old map
psi preserving/reflection E and preserving every Option-valued
ordered raw colour. These are exactly the hypotheses of a typed
embedding of the relational structures in the original binary
rectangle language, with the trivial language-symbol action.

This file connects the computationally convenient raw presentation
API to the shared AllThoseEPPA.Structure.Embedding interface, so
the EPPA witness can later be exposed as a conventional
AllThoseEPPA.Structure.IsEPPAWitness without re-proving any
combinatorial or group-valued properties.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v}
variable {U : Type w} {V : Type z}
variable {d : RawDatum G C}

/-- An injective map preserving/reflection E and preserving every
ordered raw colour literally is precisely an embedding of the
corresponding relational structures with trivial symbol action. -/
def RawRectanglePresentation.toTypedEmbedding
    (P : RawRectanglePresentation d U)
    (Q : RawRectanglePresentation d V)
    (ψ : U → V) (hinj : Function.Injective ψ)
    (hpart : ∀ x y, Q.part (ψ x) (ψ y) ↔ P.part x y)
    (hcolour : ∀ x y, Q.colour (ψ x) (ψ y) = P.colour x y) :
    Structure.Embedding
      (Language.Action.trivial (rectangleLanguage C) (Equiv.Perm (Fin 0)))
      P.toStructure Q.toStructure where
  lang := 1
  toFun := ψ
  injective := hinj
  map_rel_iff := by
    intro n R xs
    simp only [Language.Action.onRel_one]
    rcases R with ⟨name, hn⟩
    subst n
    cases name with
    | none =>
        change Q.part (ψ (xs 0)) (ψ (xs 1)) ↔
          P.part (xs 0) (xs 1)
        exact hpart _ _
    | some c =>
        change Q.colour (ψ (xs 0)) (ψ (xs 1)) = some c ↔
          P.colour (xs 0) (xs 1) = some c
        rw [hcolour]
  map_func := by
    intro n F xs
    exact PEmpty.elim F

@[simp] theorem RawRectanglePresentation.toTypedEmbedding_apply
    (P : RawRectanglePresentation d U)
    (Q : RawRectanglePresentation d V)
    (ψ : U → V) (hinj : Function.Injective ψ)
    (hpart : ∀ x y, Q.part (ψ x) (ψ y) ↔ P.part x y)
    (hcolour : ∀ x y, Q.colour (ψ x) (ψ y) = P.colour x y)
    (x : U) :
    P.toTypedEmbedding Q ψ hinj hpart hcolour x = ψ x :=
  rfl

end SemigenericEPPA
