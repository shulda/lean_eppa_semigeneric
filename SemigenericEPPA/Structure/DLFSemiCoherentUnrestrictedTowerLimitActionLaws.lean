import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitAction

/-!
# Unrestricted semi-coherent tower limit action: LimitActionLaws

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

/-- Unit law for each canonical old vertex in the actual limit. -/
theorem limitAct_one_of (T : FiniteRawActionPairTower d V)
    (i : ℕ) (x : V i) :
    T.limitAct (1 : T.GroupLimit) (T.vertexOf i x) =
      T.vertexOf i x := by
  have hOne : (1 : T.GroupLimit) = T.groupOf i 1 :=
    DirectLimit.one_def (f := T.groupTransition) i
  rw [hOne, T.limitAct_of]
  simp

/-- The action of the identity of the group DIRECT LIMIT
fixes every vertex of the vertex DIRECT LIMIT. -/
theorem limitAct_one (T : FiniteRawActionPairTower d V)
    (x : T.VertexLimit) :
    T.limitAct (1 : T.GroupLimit) x = x := by
  induction x using DirectLimit.induction with
  | _ i x =>
      exact T.limitAct_one_of i x

/-- Multiplication already acts correctly on every common-stage
triple of representatives; no group structure is assumed on the
vertex direct limit itself. -/
theorem limitAct_mul_of (T : FiniteRawActionPairTower d V)
    (i : ℕ) (h k : (T.stage i).subgroup) (x : V i) :
    T.limitAct (T.groupOf i h * T.groupOf i k) (T.vertexOf i x) =
      T.limitAct (T.groupOf i h)
        (T.limitAct (T.groupOf i k) (T.vertexOf i x)) := by
  have hMul : T.groupOf i h * T.groupOf i k = T.groupOf i (h * k) := by
    change (⟦⟨i, h⟩⟧ : T.GroupLimit) * ⟦⟨i, k⟩⟧ = ⟦⟨i, h * k⟩⟧
    exact DirectLimit.mul_def (f := T.groupTransition) i h k
  rw [hMul, T.limitAct_of, T.limitAct_of, T.limitAct_of]
  change T.vertexOf i ((h.val.val * k.val.val) x) =
    T.vertexOf i (h.val.val (k.val.val x))
  simp only [Equiv.Perm.mul_apply]

end FiniteRawActionPairTower
end SemigenericEPPA
