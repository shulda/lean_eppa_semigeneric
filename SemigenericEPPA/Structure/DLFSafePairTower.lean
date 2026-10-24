import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings

/-!
# Iterating finite safe pairs with exact structure/group embeddings

The positive DLF chain uses a sequence (Aₙ,Hₙ) of finite safe
original-language raw rectangles, and at each step an injective
induced E/R_c embedding together with an injective group
homomorphism, strictly equivariant on the old carrier.

Unlike an abstract family of finite groups, these maps are
coupled to the actual vertex embeddings. The group action
thus remains well-defined on every finite stage of a future
direct limit.

This module packages the chain and constructs a coherent
FINITE-STAGE map from Aₙ to Aₘ for every n≤m, by actual
composition of the one-step morphisms. No countable direct
limit or density theorem is asserted here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

/-- A genuine sequence of finite safe original-language pairs
with exact injective and equivariant successive morphisms. -/
structure FiniteSafeRawPairTower
    (d : RawDatum G C) (V : ℕ → Type w)
    [∀ n, Finite (V n)] where
  stage : ∀ n : ℕ, FiniteSafeRawPair d (V n)
  step : ∀ n : ℕ,
    FiniteSafeRawPairEmbedding (stage n) (stage (n + 1))

namespace FiniteSafeRawPairTower

/-- Composite morphism between arbitrary comparable finite stages.
The group map is injective and the structure embedding is induced,
and the two commute EXACTLY on all old vertices. -/
def between
    (T : FiniteSafeRawPairTower d V)
    (n m : ℕ) (h : n ≤ m) :
    FiniteSafeRawPairEmbedding (T.stage n) (T.stage m) :=
  Nat.leRecOn h
    (@fun k (f : FiniteSafeRawPairEmbedding (T.stage n) (T.stage k)) =>
      FiniteSafeRawPairEmbedding.comp f (T.step k))
    (FiniteSafeRawPairEmbedding.refl (T.stage n))

/-- Between a stage and itself, both vertex and group maps are
the strict identity. -/
theorem between_self_vertex
    (T : FiniteSafeRawPairTower d V)
    (n : ℕ) (x : V n) :
    (T.between n n le_rfl).vertex x = x := by
  simp [between, Nat.leRecOn_self, FiniteSafeRawPairEmbedding.refl]

theorem between_self_group
    (T : FiniteSafeRawPairTower d V)
    (n : ℕ) (h : (T.stage n).subgroup) :
    (T.between n n le_rfl).groupMap h = h := by
  simp [between, Nat.leRecOn_self, FiniteSafeRawPairEmbedding.refl]

/-- Every element of an early finite group has a specified
homomorphic extension to any later stage, exactly intertwining
the induced embedding of every old vertex. -/
theorem between_group_action
    (T : FiniteSafeRawPairTower d V)
    (n m : ℕ) (hnm : n ≤ m)
    (h : (T.stage n).subgroup) (x : V n) :
    ((T.between n m hnm).groupMap h).val.val
        ((T.between n m hnm).vertex x) =
      (T.between n m hnm).vertex (h.val.val x) :=
  (T.between n m hnm).group_action h x

/-- The underlying map Vₙ→Vₘ is induced in the literal raw
language: every ordered E relation and Option-valued colour
is preserved AND reflected. -/
theorem between_exact_raw
    (T : FiniteSafeRawPairTower d V)
    (n m : ℕ) (hnm : n ≤ m) (x y : V n) :
    ((T.stage m).raw.part
        ((T.between n m hnm).vertex x)
        ((T.between n m hnm).vertex y) ↔
      (T.stage n).raw.part x y) ∧
    (T.stage m).raw.colour
        ((T.between n m hnm).vertex x)
        ((T.between n m hnm).vertex y) =
      (T.stage n).raw.colour x y :=
  ⟨(T.between n m hnm).part_iff x y,
   (T.between n m hnm).colour_eq x y⟩

end FiniteSafeRawPairTower
end SemigenericEPPA
