import SemigenericEPPA.Structure.DLFFiniteUnrestrictedSemiCoherentEP

/-!
# Generic non-safe finite subgroup-action towers for semi-coherent EP

The countable semi-coherent-to-DLF implication cannot silently
assume that the selected finite group action pairs are locally
safe. We therefore keep the subgroup action and its exact
original E/R_c structure while FORGETTING all safety predicates.

This module gives actual induced equivariant embeddings of arbitrary
finite original-raw action pairs, including the identity and
strict composition, then the finite-stage n→m action/vertex
morphisms of a genuinely arbitrary finite group-action tower.

These finite-stage statements are independent of the DLF
good-orbit condition. The quotient colimit and its actual
automorphism group are the next formalization gate.
-/

namespace SemigenericEPPA

universe u v w w' w''
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

namespace FiniteRawActionPairEmbedding

variable {V : Type w} [Finite V]
variable {W : Type w'} [Finite W]
variable {X : Type w''} [Finite X]
variable {A : FiniteRawActionPair d V}
variable {B : FiniteRawActionPair d W}
variable {D : FiniteRawActionPair d X}

/-- Identity raw action-pair morphism in the actual original language. -/
def refl (A : FiniteRawActionPair d V) :
    FiniteRawActionPairEmbedding A A where
  vertex := id
  vertex_injective := Function.injective_id
  part_iff := by
    intro x y
    exact Iff.rfl
  colour_eq := by
    intro x y
    rfl
  groupMap := MonoidHom.id A.subgroup
  group_injective := by
    intro h k hh
    exact hh
  group_action := by
    intro h x
    rfl

/-- Composition respects BOTH strict group laws and the literal
original vertex relations, and is equivariant on every old vertex. -/
def comp
    (f : FiniteRawActionPairEmbedding A B)
    (g : FiniteRawActionPairEmbedding B D) :
    FiniteRawActionPairEmbedding A D where
  vertex := fun x => g.vertex (f.vertex x)
  vertex_injective := g.vertex_injective.comp f.vertex_injective
  part_iff := by
    intro x y
    exact (g.part_iff (f.vertex x) (f.vertex y)).trans (f.part_iff x y)
  colour_eq := by
    intro x y
    exact (g.colour_eq (f.vertex x) (f.vertex y)).trans (f.colour_eq x y)
  groupMap := g.groupMap.comp f.groupMap
  group_injective := g.group_injective.comp f.group_injective
  group_action := by
    intro h x
    change (g.groupMap (f.groupMap h)).val.val (g.vertex (f.vertex x)) =
      g.vertex (f.vertex (h.val.val x))
    rw [g.group_action (f.groupMap h) (f.vertex x), f.group_action h x]

/-- Literal vertex map of a composed raw action-pair embedding. -/
theorem comp_vertex_apply
    (f : FiniteRawActionPairEmbedding A B)
    (g : FiniteRawActionPairEmbedding B D)
    (x : V) :
    (comp f g).vertex x = g.vertex (f.vertex x) := rfl

/-- Literal group map of a composed raw action-pair embedding. -/
theorem comp_group_apply
    (f : FiniteRawActionPairEmbedding A B)
    (g : FiniteRawActionPairEmbedding B D)
    (h : A.subgroup) :
    (comp f g).groupMap h = g.groupMap (f.groupMap h) := rfl


end FiniteRawActionPairEmbedding

variable {V : ℕ → Type w} [∀ n, Finite (V n)]

/-- A genuine sequence of arbitrary finite original-language action pairs
with exact injective and equivariant successive morphisms. -/
structure FiniteRawActionPairTower
    (d : RawDatum G C) (V : ℕ → Type w)
    [∀ n, Finite (V n)] where
  stage : ∀ n : ℕ, FiniteRawActionPair d (V n)
  step : ∀ n : ℕ,
    FiniteRawActionPairEmbedding (stage n) (stage (n + 1))

namespace FiniteRawActionPairTower

/-- Composite morphism between arbitrary comparable finite stages.
The group map is injective and the structure embedding is induced,
and the two commute EXACTLY on all old vertices. -/
def between
    (T : FiniteRawActionPairTower d V)
    (n m : ℕ) (h : n ≤ m) :
    FiniteRawActionPairEmbedding (T.stage n) (T.stage m) :=
  Nat.leRecOn h
    (@fun k (f : FiniteRawActionPairEmbedding (T.stage n) (T.stage k)) =>
      FiniteRawActionPairEmbedding.comp f (T.step k))
    (FiniteRawActionPairEmbedding.refl (T.stage n))

/-- Between a stage and itself, both vertex and group maps are
the strict identity. -/
theorem between_self_vertex
    (T : FiniteRawActionPairTower d V)
    (n : ℕ) (x : V n) :
    (T.between n n le_rfl).vertex x = x := by
  simp [between, Nat.leRecOn_self, FiniteRawActionPairEmbedding.refl]

theorem between_self_group
    (T : FiniteRawActionPairTower d V)
    (n : ℕ) (h : (T.stage n).subgroup) :
    (T.between n n le_rfl).groupMap h = h := by
  simp [between, Nat.leRecOn_self, FiniteRawActionPairEmbedding.refl]

/-- Every element of an early finite group has a specified
homomorphic extension to any later stage, exactly intertwining
the induced embedding of every old vertex. -/
theorem between_group_action
    (T : FiniteRawActionPairTower d V)
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
    (T : FiniteRawActionPairTower d V)
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


end FiniteRawActionPairTower

end SemigenericEPPA
