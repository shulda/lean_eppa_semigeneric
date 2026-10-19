import SemigenericEPPA.Bridge.UpstreamToExactRawGroupoid

/-!
# Recover exact groupoid source/range and composition from upstream API

The shared AllThoseEPPA coherent-EPPA vocabulary uses two crucial
relations on partial automorphisms:

* Equivalent: same language action and same partial map on exactly
  the same source (not equality of irrelevant off-domain values);
* CoherentTriple f g h: exact target(f)=source(g), while h is
  Equivalent to the genuine composition g∘f.

The raw groupoid developed here uses exact induced subset arrows.
This module checks that the upstream predicates imply precisely
the equalities required to transport the raw groupoid functor:
same exact source, same exact target, pointwise equality on the
source, and strict pointwise composition for coherent triples.

No ordinary EPPA or coherent functor is used to prove these facts.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v}
variable {A : Type w} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Equivalent upstream partial automorphisms agree on their
actual domain, and have not only equal sources but ALSO equal
targets, as a consequence of their partial-equivalence laws. -/
theorem upstreamEquivalent_exactSourceTarget
    (P : RawRectanglePresentation d A)
    (p q : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (heq : Structure.PartialIsomorphism.Equivalent p q) :
    p.source = q.source ∧
    p.target = q.target ∧
    (∀ x : A, x ∈ p.source → p x = q x) := by
  have hPartial := heq.2
  refine ⟨hPartial.source_eq, hPartial.target_eq, ?_⟩
  intro x hx
  exact hPartial.eqOn x hx

/-- A coherent triple of upstream partial automorphisms is
literally an exact composition on sources, ranges and old points.
No restriction of the composed domain is permitted. -/
theorem upstreamCoherentTriple_exactComposition
    (P : RawRectanglePresentation d A)
    (f g h : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure)
    (hcoh : Structure.PartialIsomorphism.CoherentTriple f g h) :
    f.target = g.source ∧
    h.source = f.source ∧
    h.target = g.target ∧
    (∀ x : A, x ∈ f.source → h x = g (f x)) := by
  obtain ⟨htg, hEquivalent⟩ := hcoh
  have hSource : h.source = (g.comp f htg).source :=
    hEquivalent.2.source_eq
  have hTarget : h.target = (g.comp f htg).target :=
    hEquivalent.2.target_eq
  have hApply (x : A) (hx : x ∈ f.source) :
      h x = (g.comp f htg) x := by
    exact hEquivalent.2.eqOn x (by
      simpa only [hSource] using hx)
  refine ⟨htg, ?_, ?_, ?_⟩
  · exact hSource
  · exact hTarget
  · intro x hx
    have ht : x ∈ h.source := by
      rw [hSource]
      exact hx
    have heq : h x = (g.comp f htg) x :=
      hEquivalent.2.eqOn x ht
    exact heq

end RawRectanglePresentation

end SemigenericEPPA
