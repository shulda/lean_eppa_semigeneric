import SemigenericEPPA.Classification.RuleMatrixPresentation

/-!
# Literal induced embeddings between two-part matrix structures

Injective maps on row and column index sets which preserve each raw
matrix entry induce true original-language embeddings (both E and
every directed R_c), not merely graph homomorphisms. These are used
to instantiate strong amalgamation on tiny witness spans.
-/

namespace SemigenericEPPA.Classification

open AllThoseEPPA

universe u

namespace RectangleRule

variable {C X Y X' Y' : Type u} (R : RectangleRule C)

/-- Extend row/column maps to the two-part vertex carrier. -/
def matrixMap (fx : X → X') (fy : Y → Y') :
    (X ⊕ Y) → (X' ⊕ Y')
  | .inl x => .inl (fx x)
  | .inr y => .inr (fy y)

theorem matrixMap_injective
    (fx : X → X') (fy : Y → Y')
    (hfx : Function.Injective fx) (hfy : Function.Injective fy) :
    Function.Injective (matrixMap fx fy) := by
  intro v w hvw
  cases v <;> cases w <;>
    simp_all [matrixMap]
  · exact hfx hvw
  · exact hfy hvw

theorem matrixMap_part_iff
    (fx : X → X') (fy : Y → Y')
    (v w : X ⊕ Y) :
    matrixPart v w ↔ matrixPart (matrixMap fx fy v) (matrixMap fx fy w) := by
  cases v <;> cases w <;>
    simp [matrixPart, matrixMap]

theorem matrixMap_colour
    (fx : X → X') (fy : Y → Y')
    (M : X → Y → C) (M' : X' → Y' → C)
    (hM : ∀ x y, M' (fx x) (fy y) = M x y)
    (v w : X ⊕ Y) :
    R.matrixColour M' (matrixMap fx fy v) (matrixMap fx fy w) =
      R.matrixColour M v w := by
  cases v <;> cases w <;>
    simp [matrixColour, matrixMap, hM]

/-- Literal embedding of E and every R_c in both directions. -/
noncomputable def matrixEmbedding
    (c₀ : C)
    (fx : X → X') (fy : Y → Y')
    (hfx : Function.Injective fx)
    (hfy : Function.Injective fy)
    (M : X → Y → C) (M' : X' → Y' → C)
    (hM : ∀ x y, M' (fx x) (fy y) = M x y) :
    Structure.Embedding (rectangleTrivialAction C)
      (R.matrixStructure c₀ M) (R.matrixStructure c₀ M') :=
  embeddingOfPairwiseEquiv (rectangleTrivialAction C)
    (R.matrixStructure c₀ M) (R.matrixStructure c₀ M')
    (matrixMap fx fy)
    (matrixMap_injective fx fy hfx hfy)
    (by
      intro v w
      exact ((R.matrixStructure_part c₀ M v w).trans
        ((matrixMap_part_iff fx fy v w).trans
          (R.matrixStructure_part c₀ M' _ _).symm)).symm)
    (by
      intro c v w
      rw [R.matrixStructure_colour c₀ c M v w,
        R.matrixStructure_colour c₀ c M'
          (matrixMap fx fy v) (matrixMap fx fy w),
        R.matrixMap_colour fx fy M M' hM v w])

@[simp] theorem matrixEmbedding_inl
    (c₀ : C)
    (fx : X → X') (fy : Y → Y')
    (hfx : Function.Injective fx) (hfy : Function.Injective fy)
    (M : X → Y → C) (M' : X' → Y' → C)
    (hM : ∀ x y, M' (fx x) (fy y) = M x y) (x : X) :
    R.matrixEmbedding c₀ fx fy hfx hfy M M' hM (.inl x) =
      .inl (fx x) := rfl

@[simp] theorem matrixEmbedding_inr
    (c₀ : C)
    (fx : X → X') (fy : Y → Y')
    (hfx : Function.Injective fx) (hfy : Function.Injective fy)
    (M : X → Y → C) (M' : X' → Y' → C)
    (hM : ∀ x y, M' (fx x) (fy y) = M x y) (y : Y) :
    R.matrixEmbedding c₀ fx fy hfx hfy M M' hM (.inr y) =
      .inr (fy y) := rfl

end RectangleRule
end SemigenericEPPA.Classification
