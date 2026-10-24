import SemigenericEPPA.Structure.DLFSafePairTowerDirectedLimits
import Mathlib.Data.Finset.Basic

/-!
# Finite subsets of a genuine DLF vertex colimit are supported by one stage

Every finite set of vertices in the quotient directed limit comes
from a common finite original-language stage. This is the exact
finite-support lemma required later to approximate a global
automorphism on F by an element of a finite safe subgroup: both F
and its image can be represented at one sufficiently late stage.

No direct-limit homogeneity, group action, or density is assumed here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Every FINITE subset of the actual quotient vertex limit lies
inside the canonical image of some single finite stage. -/
theorem finiteSubset_supportedAtStage
    (T : FiniteSafeRawPairTower d V)
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

end FiniteSafeRawPairTower
end SemigenericEPPA
