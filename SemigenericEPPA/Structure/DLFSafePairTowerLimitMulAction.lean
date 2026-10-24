import SemigenericEPPA.Structure.DLFSafePairTowerLimitActionLaws

/-!
# The actual group colimit acts on the actual vertex colimit

Finite safe-pair morphisms are strictly equivariant; hence the
well-defined quotient-limit binary evaluation from the preceding
module satisfies the actual group-action laws. For multiplication,
transport ANY independent group/group/vertex representatives to
a SINGLE common finite stage, where the permutation group law
holds exactly. This constructs a genuine MulAction, and thereby a
natural homomorphism from the group colimit to permutations of the
vertex colimit.

Faithfulness, original raw-relation invariance, Fraisse homogeneity
and topological density are separate remaining obligations.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Multiplication law for arbitrary, independently represented
group colimit elements and an arbitrary vertex colimit element. -/
theorem limitAct_mul (T : FiniteSafeRawPairTower d V)
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
    (T : FiniteSafeRawPairTower d V) :
    MulAction T.GroupLimit T.VertexLimit where
  smul := T.limitAct
  one_smul := T.limitAct_one
  mul_smul := T.limitAct_mul

/-- The action agrees with EVERY old finite raw automorphism
on canonical stage images, now with the actual MulAction notation. -/
theorem groupLimit_smul_vertexOf
    (T : FiniteSafeRawPairTower d V)
    (i : ℕ) (h : (T.stage i).subgroup) (x : V i) :
    (T.groupOf i h) • (T.vertexOf i x) =
      T.vertexOf i (h.val.val x) :=
  T.limitAct_of i h x

end FiniteSafeRawPairTower
end SemigenericEPPA
