import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerDirectedLimits
import Mathlib.Data.Finset.Basic

/-!
# Unrestricted semi-coherent actual automorphism limit: FiniteSupport

The stagewise safe-pair colimit theorem is replayed on an arbitrary
finite original-raw group-action tower. Its proof only uses strict
finite subgroup actions, induced E/R_c embeddings and the
next-stage partial connector property, not local involution safety.
No claim of tower existence is made in this module.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Every FINITE subset of the actual quotient vertex limit lies
inside the canonical image of some single finite stage. -/
theorem finiteSubset_supportedAtStage
    (T : FiniteRawActionPairTower d V)
    (F : Finset T.VertexLimit) :
    ∃ n : ℕ, ∀ z : T.VertexLimit,
      z ∈ F → ∃ a : V n, T.vertexOf n a = z := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro z hz
      simp at hz
  | @insert x S hx ih =>
      obtain ⟨n, hS⟩ := ih
      obtain ⟨i, a, ha⟩ :=
        DirectLimit.exists_eq_mk (f := T.vertexTransition) x
      refine ⟨max i n, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with hzx | hzS
      · subst z
        refine ⟨T.vertexTransition i (max i n)
          (le_max_left i n) a, ?_⟩
        exact (T.vertexOf_transition i (max i n)
          (le_max_left i n) a).trans ha.symm
      · obtain ⟨b, hb⟩ := hS z hzS
        refine ⟨T.vertexTransition n (max i n)
          (le_max_right i n) b, ?_⟩
        exact (T.vertexOf_transition n (max i n)
          (le_max_right i n) b).trans hb

end FiniteRawActionPairTower
end SemigenericEPPA
