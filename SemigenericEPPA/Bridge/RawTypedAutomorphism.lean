import SemigenericEPPA.Bridge.RawTypedEmbedding
import AllThoseEPPA.EPPA

/-!
# Literal raw automorphisms in the general AllThoseEPPA API

A permutation preserving/reflection the distinguished E relation
and preserving every ordered raw colour defines an automorphism
of the exact original binary relational structure, with identity
symbol-action component.

This conversion is deliberately stated separately from existence
of EPPA witnesses, so the concrete raw valuation automorphisms
can be reused in other typed formalization projects through
AllThoseEPPA.Structure.Automorphism.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- An exact raw-colour preserving permutation gives a genuine typed
total automorphism in the general language-action infrastructure. -/
def RawRectanglePresentation.toTypedAutomorphism
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hpart : ∀ x y, P.part (T x) (T y) ↔ P.part x y)
    (hcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y) :
    Structure.Automorphism
      (Language.Action.trivial (rectangleLanguage C) PUnit)
      P.toStructure := by
  let emb := P.toTypedEmbedding P T T.injective hpart hcolour
  refine {
    toPartialIsomorphism := {
      lang := 1
      toPartialEquiv := T.toPartialEquiv
      source_closed := ?_
      target_closed := ?_
      map_rel_iff := ?_
      map_func := ?_ }
    source_eq_univ := rfl
    target_eq_univ := rfl }
  · exact P.toStructure.isClosed_univ
  · exact P.toStructure.isClosed_univ
  · intro n R xs hxs
    exact emb.map_rel_iff R xs
  · intro n F xs hxs
    exact PEmpty.elim F

@[simp] theorem RawRectanglePresentation.toTypedAutomorphism_apply
    (P : RawRectanglePresentation d V)
    (T : Equiv.Perm V)
    (hpart : ∀ x y, P.part (T x) (T y) ↔ P.part x y)
    (hcolour : ∀ x y, P.colour (T x) (T y) = P.colour x y)
    (x : V) :
    P.toTypedAutomorphism T hpart hcolour x = T x :=
  rfl

end SemigenericEPPA
