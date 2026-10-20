import SemigenericEPPA.Bridge.UpstreamCoherentTripleExact
import SemigenericEPPA.Bridge.UpstreamToExactRawGroupoid

/-!
# Functorial correspondence between upstream partial maps and exact raw arrows

The upstream AllThoseEPPA coherent EPPA API uses PartialEquiv and
identifies maps under EqOnSource, discarding arbitrary off-domain
values. Our raw groupoid instead uses literal induced-set
isomorphisms with exactly matching source and target.

We certify both missing compatibility laws:

* Equivalent upstream maps become EQUAL raw groupoid arrows,
  after identifying their exactly equal source and target sets.
* Composition of upstream maps on an exactly matching source/range
  becomes LITERALLY the exact groupoid composition.

These facts allow the already certified coherent functor on the
exact raw groupoid to satisfy the upstream respects_equivalent
and CoherentTriple axioms without any ad hoc shrinking of domains.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {A : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- General heterogeneous extensionality for exact raw isomorphisms
over EQUAL old source and target subsets, without trying to eliminate
equalities between arbitrary projections of upstream PartialEquiv. -/
private theorem exactRawArrow_heq_of_pointwise
    (P : RawRectanglePresentation d A)
    {S S' T T' : Set A}
    (hS : S = S') (hT : T = T')
    (f : ExactPartialIso P S T)
    (g : ExactPartialIso P S' T')
    (hMap : ∀ (x : A) (hx : x ∈ S) (hx' : x ∈ S'),
      (f.toEquiv ⟨x, hx⟩).val =
        (g.toEquiv ⟨x, hx'⟩).val) :
    HEq f g := by
  cases hS
  cases hT
  apply heq_of_eq
  apply ExactPartialIso.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact hMap x.val x.property x.property

/-- Equivalent upstream partial raw maps have the same exact
raw groupoid arrow (after identifying their sources and targets). -/
theorem upstreamToExactRawArrow_equivalent
    (P : RawRectanglePresentation d A)
    (p q : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (heq : Structure.PartialIsomorphism.Equivalent p q) :
    HEq (P.upstreamToExactRawArrow p)
      (P.upstreamToExactRawArrow q) := by
  obtain ⟨hsrc, htgt, hmap⟩ :=
    P.upstreamEquivalent_exactSourceTarget p q heq
  apply exactRawArrow_heq_of_pointwise P hsrc htgt
    (P.upstreamToExactRawArrow p)
    (P.upstreamToExactRawArrow q)
  intro x hx hx'
  exact hmap x hx

/-- Transporting the TARGET subset of an exact raw arrow does
not alter the underlying old vertex map. Kept separate to eliminate
the dependent equality proof before the composition calculation. -/
private theorem exactRawArrow_cast_target_val
    (P : RawRectanglePresentation d A)
    {S T T' : Set A}
    (f : ExactPartialIso P S T)
    (h : T = T')
    (x : S) :
    ((h ▸ f : ExactPartialIso P S T').toEquiv x).val =
      (f.toEquiv x).val := by
  cases h
  rfl

/-- Exact upstream composition agrees with literal raw groupoid
composition, transporting only the intermediate target subset.
Unlike generalizing the source or target of a partial equivalence,
this proof does not change the dependent type of g.comp f htg. -/
theorem upstreamToExactRawArrow_comp
    (P : RawRectanglePresentation d A)
    (f g : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (htg : f.target = g.source) :
    HEq (P.upstreamToExactRawArrow (g.comp f htg))
      ((P.upstreamToExactRawArrow g).comp
        (htg ▸ P.upstreamToExactRawArrow f)) := by
  apply heq_of_eq
  apply ExactPartialIso.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change g (f x.val) =
    g (((htg ▸ P.upstreamToExactRawArrow f).toEquiv x).val)
  rw [exactRawArrow_cast_target_val P
    (P.upstreamToExactRawArrow f) htg x]

end RawRectanglePresentation

end SemigenericEPPA
