import SemigenericEPPA.Structure.DLFSafePairTowerDirectedLimits

/-!
# The canonical finite-stage-compatible action on both DLF colimits

The directed group-limit elements are represented by actual finite
automorphisms h ∈ H_i; the vertex-limit elements are represented by
original-language vertices x ∈ V_j. To let the former act on the
latter, move both to a common later stage, act there, and pass to
the quotient. Mathlib's `DirectLimit.map₂` enforces well-definedness.

The required compatibility identity is EXACTLY the strict equivariance
of every finite safe-pair embedding, and does not involve any
additional EPPA or colour choice. In this module the action is
constructed as a binary map and certified on common-stage
representatives. The MulAction laws, raw relation invariance and
density will be proved separately.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- The true well-defined group-limit-on-vertex-limit evaluation
induced by STRICT finite-stage equivariance. -/
noncomputable def limitAct (T : FiniteSafeRawPairTower d V) :
    T.GroupLimit → T.VertexLimit → T.VertexLimit :=
  DirectLimit.map₂ T.groupTransition T.vertexTransition
    T.vertexTransition
    (fun i (h : (T.stage i).subgroup) (x : V i) => h.val.val x)
    (by
      intro i j hij h x
      exact ((T.between i j hij).group_action h x).symm)

/-- This action agrees exactly with the old automorphism-group
action on every original finite stage, on its canonical images. -/
theorem limitAct_of (T : FiniteSafeRawPairTower d V)
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

end FiniteSafeRawPairTower
end SemigenericEPPA
