import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitAction
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitRawData

/-!
# Unrestricted semi-coherent tower limit action: LimitRawAction

The source Lean proof is independent of the local safety certificate.
We reuse strict induced original E/R_c embeddings and faithful
finite acting group morphisms for an arbitrary finite action tower.
Full Lean CI and axiom audit required.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- A genuine element of the group colimit and TWO genuine vertices
have representatives at one common finite stage. Both group and
vertex transition maps are the original strictly equivariant maps. -/
theorem exists_group_two_vertices_at_sameStage
    (T : FiniteRawActionPairTower d V)
    (g : T.GroupLimit) (x y : T.VertexLimit) :
    ∃ (n : ℕ) (h : (T.stage n).subgroup) (a b : V n),
      g = T.groupOf n h ∧
      x = T.vertexOf n a ∧
      y = T.vertexOf n b := by
  obtain ⟨i, h, hg⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  obtain ⟨j, a, hx⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) x
  obtain ⟨k, b, hy⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) y
  let n : ℕ := max i (max j k)
  have hi : i ≤ n := le_max_left i (max j k)
  have hj : j ≤ n :=
    (le_max_left j k).trans (le_max_right i (max j k))
  have hk : k ≤ n :=
    (le_max_right j k).trans (le_max_right i (max j k))
  refine ⟨n, T.groupTransition i n hi h,
    T.vertexTransition j n hj a,
    T.vertexTransition k n hk b, ?_, ?_, ?_⟩
  · exact hg.trans (T.groupOf_transition i n hi h).symm
  · exact hx.trans (T.vertexOf_transition j n hj a).symm
  · exact hy.trans (T.vertexOf_transition k n hk b).symm

/-- Every group-colimit element preserves AND reflects the original
E-equivalence relation on the vertex-colimit, not only its reduct. -/
theorem limitAct_part_iff
    (T : FiniteRawActionPairTower d V)
    (g : T.GroupLimit) (x y : T.VertexLimit) :
    T.limitPart (T.limitAct g x) (T.limitAct g y) ↔
      T.limitPart x y := by
  obtain ⟨n, h, a, b, rfl, rfl, rfl⟩ :=
    T.exists_group_two_vertices_at_sameStage g x y
  change T.limitPart
      (T.limitAct (T.groupOf n h) (T.vertexOf n a))
      (T.limitAct (T.groupOf n h) (T.vertexOf n b)) ↔
    T.limitPart (T.vertexOf n a) (T.vertexOf n b)
  rw [T.limitAct_of, T.limitAct_of, T.limitPart_of, T.limitPart_of]
  exact (T.stage n).raw.fullRawAutGroup_part h.val a b

/-- The group-colimit action preserves every literal ordered raw
colour R_c simultaneously. No effective-colour replacement. -/
theorem limitAct_colour_eq
    (T : FiniteRawActionPairTower d V)
    (g : T.GroupLimit) (x y : T.VertexLimit) :
    T.limitColour (T.limitAct g x) (T.limitAct g y) =
      T.limitColour x y := by
  obtain ⟨n, h, a, b, rfl, rfl, rfl⟩ :=
    T.exists_group_two_vertices_at_sameStage g x y
  change T.limitColour
      (T.limitAct (T.groupOf n h) (T.vertexOf n a))
      (T.limitAct (T.groupOf n h) (T.vertexOf n b)) =
    T.limitColour (T.vertexOf n a) (T.vertexOf n b)
  rw [T.limitAct_of, T.limitAct_of, T.limitColour_of, T.limitColour_of]
  exact (T.stage n).raw.fullRawAutGroup_colour h.val a b

end FiniteRawActionPairTower
end SemigenericEPPA
