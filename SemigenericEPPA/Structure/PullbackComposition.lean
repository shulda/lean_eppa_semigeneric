import SemigenericEPPA.Structure.Pullback

/-!
# Exact composition and extensionality of literal original-language pullbacks

The finite-SAP normalization uses consecutive bijective renamings:
first a finite complement normalization, then successive prefix
inclusions. Their pullback structures are IDENTICAL to the one-step
induced pullback along the composite vertex map, not merely
isomorphic. No model-theoretic assumptions enter this lemma.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {C : Type u} {X : Type v} {Y : Type w} {Z : Type z}

/-- Pulling back twice along actual vertex maps is EXACTLY the
pullback along their composite, for every original E/R_c symbol. -/
theorem pullbackRectangle_comp
    (A : Structure (rectangleLanguage C) X)
    (f : Y → X) (g : Z → Y) :
    pullbackRectangle (pullbackRectangle A f) g =
      pullbackRectangle A (f ∘ g) := by
  rfl

/-- Pointwise equal vertex maps induce LITERALLY identical
original-language structures, including all ordered raw predicates. -/
theorem pullbackRectangle_congr
    (A : Structure (rectangleLanguage C) X)
    (f g : Y → X) (h : ∀ y, f y = g y) :
    pullbackRectangle A f = pullbackRectangle A g := by
  have hfg : f = g := funext h
  rw [hfg]

end SemigenericEPPA
