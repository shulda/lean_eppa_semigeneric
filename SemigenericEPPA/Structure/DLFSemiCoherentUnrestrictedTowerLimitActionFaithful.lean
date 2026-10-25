import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitMulAction

/-!
# Unrestricted semi-coherent tower limit action: LimitActionFaithful

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

/-- A group-limit element that fixes all genuine colimit vertices
is literally the identity in the group-limit group. -/
theorem limitAct_faithful
    (T : FiniteRawActionPairTower d V)
    (g : T.GroupLimit)
    (hg : ∀ x : T.VertexLimit, T.limitAct g x = x) :
    g = 1 := by
  obtain ⟨n, h, hh⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  have hFix : ∀ x : V n, h.val.val x = x := by
    intro x
    have hz := hg (T.vertexOf n x)
    rw [hh] at hz
    change T.limitAct (T.groupOf n h) (T.vertexOf n x) =
      T.vertexOf n x at hz
    rw [T.limitAct_of] at hz
    exact T.vertexOf_injective n hz
  have hPerm : h.val.val = 1 := by
    ext x
    simpa only [Equiv.Perm.coe_one, id_eq] using hFix x
  have hOne : h = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hPerm
  calc
    g = T.groupOf n h := hh
    _ = T.groupOf n 1 := by rw [hOne]
    _ = 1 := (DirectLimit.one_def (f := T.groupTransition) n).symm

end FiniteRawActionPairTower
end SemigenericEPPA
