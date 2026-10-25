import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitActionLaws

/-!
# Unrestricted semi-coherent tower limit action: LimitMulAction

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

/-- Multiplication law for arbitrary, independently represented
group colimit elements and an arbitrary vertex colimit element. -/
theorem limitAct_mul (T : FiniteRawActionPairTower d V)
    (g h : T.GroupLimit) (x : T.VertexLimit) :
    T.limitAct (g * h) x =
      T.limitAct g (T.limitAct h x) := by
  obtain ⟨i, a, ha⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  obtain ⟨j, b, hb⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) h
  obtain ⟨l, v, hv⟩ :=
    DirectLimit.exists_eq_mk (f := T.vertexTransition) x
  subst g
  subst h
  subst x
  let n : ℕ := max (max i j) l
  have hi : i ≤ n :=
    (le_max_left i j).trans (le_max_left (max i j) l)
  have hj : j ≤ n :=
    (le_max_right i j).trans (le_max_left (max i j) l)
  have hl : l ≤ n := le_max_right (max i j) l
  change T.limitAct (T.groupOf i a * T.groupOf j b)
    (T.vertexOf l v) =
      T.limitAct (T.groupOf i a)
        (T.limitAct (T.groupOf j b) (T.vertexOf l v))
  rw [← T.groupOf_transition i n hi a,
      ← T.groupOf_transition j n hj b,
      ← T.vertexOf_transition l n hl v]
  exact T.limitAct_mul_of n
    (T.groupTransition i n hi a)
    (T.groupTransition j n hj b)
    (T.vertexTransition l n hl v)

/-- A real group action of the genuine limit of finite safe
automorphism groups on the literal vertex directed-limit carrier. -/
noncomputable instance limitMulAction
    (T : FiniteRawActionPairTower d V) :
    MulAction T.GroupLimit T.VertexLimit where
  smul := T.limitAct
  one_smul := T.limitAct_one
  mul_smul := T.limitAct_mul

/-- The action agrees with EVERY old finite raw automorphism
on canonical stage images, now with the actual MulAction notation. -/
theorem groupLimit_smul_vertexOf
    (T : FiniteRawActionPairTower d V)
    (i : ℕ) (h : (T.stage i).subgroup) (x : V i) :
    (T.groupOf i h) • (T.vertexOf i x) =
      T.vertexOf i (h.val.val x) :=
  T.limitAct_of i h x

end FiniteRawActionPairTower
end SemigenericEPPA
