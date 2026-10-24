import SemigenericEPPA.Structure.DLFSafePairTowerLimitAction
import SemigenericEPPA.Structure.DLFSafePairTowerLimitRawData

/-!
# Genuine direct-limit group action preserves original E and every ordered raw colour

A finite safe-pair tower carries its original E and Option-valued R_c
predicates to the quotient vertex colimit. Independently, the actual
finite-group colimit has a canonical well-defined evaluation action on
these vertices. Here we prove this action preserves BOTH the original
E predicate and the literal ordered Option C-colour, rather than only
the derived effective G-colour.

The proof puts a group element and TWO vertex elements at one common
finite stage. Strict stage equivariance transports all three
representatives correctly, and literal old raw automorphism laws
then give the desired equalities.

These facts do not assume the full MulAction laws or countable
Fraisse homogeneity; they are the original-language invariance gate
for the eventual faithful subgroup of Aut_raw(VertexLimit).
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- A genuine element of the group colimit and TWO genuine vertices
admit representatives at one common finite stage. Both group and
vertex transition maps are the original strictly equivariant maps. -/
theorem exists_group_two_vertices_at_sameStage
    (T : FiniteSafeRawPairTower d V)
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
    (T : FiniteSafeRawPairTower d V)
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
    (T : FiniteSafeRawPairTower d V)
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

end FiniteSafeRawPairTower
end SemigenericEPPA
