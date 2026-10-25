import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerDirectedLimits

/-!
# Unrestricted semi-coherent tower limit action: LimitAction

The source Lean proof is independent of the local safety certificate.
We reuse strict induced original E/R_c embeddings and faithful
finite acting group morphisms for an arbitrary finite action tower.
Full Lean CI and axiom audit required.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- The true well-defined group-limit-on-vertex-limit evaluation
induced by STRICT finite-stage equivariance. -/
noncomputable def limitAct (T : FiniteRawActionPairTower d V) :
    T.GroupLimit → T.VertexLimit → T.VertexLimit :=
  DirectLimit.map₂ T.groupTransition T.vertexTransition
    T.vertexTransition
    (fun i (h : (T.stage i).subgroup) (x : V i) => h.val.val x)
    (by
      intro i j hij h x
      exact ((T.between i j hij).group_action h x).symm)

/-- This action agrees exactly with the old automorphism-group
action on every original finite stage, on its canonical images. -/
theorem limitAct_of (T : FiniteRawActionPairTower d V)
    (i : ℕ) (h : (T.stage i).subgroup) (x : V i) :
    T.limitAct (T.groupOf i h) (T.vertexOf i x) =
      T.vertexOf i (h.val.val x) := by
  unfold limitAct groupOf vertexOf
  exact DirectLimit.map₂_def
    (f₁ := T.groupTransition) (f₂ := T.vertexTransition)
    (f := T.vertexTransition)
    (ih := fun j (g : (T.stage j).subgroup) (v : V j) => g.val.val v)
    (compat := by
      intro j k hjk g v
      exact ((T.between j k hjk).group_action g v).symm)
    i h x

end FiniteRawActionPairTower
end SemigenericEPPA
