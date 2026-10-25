import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerDirectedLimits

/-!
# Unrestricted semi-coherent action-tower colimit: LimitRawData

Port of the verified original-raw finite stage/group-limit theorem
from finite SAFE action pairs to arbitrary finite group-action pairs.
Only injective original E/R_c embeddings and strict equivariant
finite group homomorphisms are required. No local safety hypothesis.
The next modules will construct the actual limit action and density.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Well-defined E-relation on the honest vertex quotient colimit. -/
noncomputable def limitPart (T : FiniteRawActionPairTower d V) :
    T.VertexLimit → T.VertexLimit → Prop :=
  DirectLimit.lift₂ T.vertexTransition T.vertexTransition
    (fun i x y => (T.stage i).raw.part x y)
    (by
      intro i j hij x y
      exact propext ((T.between i j hij).part_iff x y).symm)

/-- Literal ordered raw-colour function on the same vertex limit.
The entire Option C, not only its effective group projection,
is transported exactly across the direct limit. -/
noncomputable def limitColour (T : FiniteRawActionPairTower d V) :
    T.VertexLimit → T.VertexLimit → Option C :=
  DirectLimit.lift₂ T.vertexTransition T.vertexTransition
    (fun i x y => (T.stage i).raw.colour x y)
    (by
      intro i j hij x y
      exact ((T.between i j hij).colour_eq x y).symm)

/-- E on old-stage images is literally the old E relation. -/
theorem limitPart_of (T : FiniteRawActionPairTower d V)
    (i : ℕ) (x y : V i) :
    T.limitPart (T.vertexOf i x) (T.vertexOf i y) ↔
      (T.stage i).raw.part x y := by
  simp only [limitPart, vertexOf, DirectLimit.lift₂_def]

/-- Every ordered raw R_c predicate is exactly preserved and reflected
by the canonical inclusion into the vertex colimit. -/
theorem limitColour_of (T : FiniteRawActionPairTower d V)
    (i : ℕ) (x y : V i) :
    T.limitColour (T.vertexOf i x) (T.vertexOf i y) =
      (T.stage i).raw.colour x y := by
  unfold limitColour vertexOf
  exact DirectLimit.lift₂_def
    (f₁ := T.vertexTransition) (f₂ := T.vertexTransition)
    (ih := fun j a b => (T.stage j).raw.colour a b)
    (compat := by
      intro j k hjk a b
      exact ((T.between j k hjk).colour_eq a b).symm)
    i x y

end FiniteRawActionPairTower
end SemigenericEPPA
