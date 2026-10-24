import SemigenericEPPA.Structure.DLFSafePairTowerDirectedLimits

/-!
# Actual original-language relation and colour data on the vertex colimit

For a tower of genuine finite safe R1--R3 raw structures with exact
induced embeddings, the canonical directed vertex limit must carry
well-defined E and ordered Option-valued raw R_c colours.

Mathlib's quotient direct-limit binary eliminator guarantees
well-definedness. The proof of compatibility for E uses the exact
part_iff of the actual stage embeddings; the proof for raw colours
uses literal colour_eq, not merely equality of effective G-colours.
This is the raw-data prerequisite for assembling a genuine
infinite R1--R3 presentation and its automorphism group action.

Nothing here asserts Fraisse homogeneity, SAP, density or that the
limit is already a valid RawRectanglePresentation.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Well-defined E-relation on the honest vertex quotient colimit. -/
noncomputable def limitPart (T : FiniteSafeRawPairTower d V) :
    T.VertexLimit → T.VertexLimit → Prop :=
  DirectLimit.lift₂ T.vertexTransition T.vertexTransition
    (fun i x y => (T.stage i).raw.part x y)
    (by
      intro i j hij x y
      exact propext ((T.between i j hij).part_iff x y).symm)

/-- Literal ordered raw-colour function on the same vertex limit.
The entire Option C, not only its effective group projection,
is transported exactly across the direct limit. -/
noncomputable def limitColour (T : FiniteSafeRawPairTower d V) :
    T.VertexLimit → T.VertexLimit → Option C :=
  DirectLimit.lift₂ T.vertexTransition T.vertexTransition
    (fun i x y => (T.stage i).raw.colour x y)
    (by
      intro i j hij x y
      exact ((T.between i j hij).colour_eq x y).symm)

/-- E on old-stage images is literally the old E relation. -/
theorem limitPart_of (T : FiniteSafeRawPairTower d V)
    (i : ℕ) (x y : V i) :
    T.limitPart (T.vertexOf i x) (T.vertexOf i y) ↔
      (T.stage i).raw.part x y := by
  simp only [limitPart, vertexOf, DirectLimit.lift₂_def]
  exact Iff.rfl

/-- Every ordered raw R_c predicate is exactly preserved and reflected
by the canonical inclusion into the vertex colimit. -/
theorem limitColour_of (T : FiniteSafeRawPairTower d V)
    (i : ℕ) (x y : V i) :
    T.limitColour (T.vertexOf i x) (T.vertexOf i y) =
      (T.stage i).raw.colour x y := by
  simp only [limitColour, vertexOf, DirectLimit.lift₂_def]

end FiniteSafeRawPairTower
end SemigenericEPPA
