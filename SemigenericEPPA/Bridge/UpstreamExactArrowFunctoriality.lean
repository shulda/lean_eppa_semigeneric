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
  cases hsrc
  cases htgt
  apply HEq.rfl_of_eq
  apply ExactPartialIso.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact hmap x.val x.property

/-- Exact upstream composition is EQUAL to exact raw groupoid
composition. In particular the composite has no shrunken source. -/
theorem upstreamToExactRawArrow_comp
    (P : RawRectanglePresentation d A)
    (f g : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (htg : f.target = g.source) :
    HEq (P.upstreamToExactRawArrow (g.comp f htg))
      ((P.upstreamToExactRawArrow g).comp
        (P.upstreamToExactRawArrow f)) := by
  cases htg
  apply HEq.rfl_of_eq
  apply ExactPartialIso.ext
  apply Equiv.ext
  intro x
  rfl

end RawRectanglePresentation

end SemigenericEPPA
