import SemigenericEPPA.Structure.DLFSafePairTowerTransitivity
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Genuine directed vertex and group limits of safe-pair towers

An ascending tower of finite safe pairs comes with honest injective
original-language vertex embeddings and injective homomorphisms of
finite automorphism groups. The strict three-stage cocycles give
actual mathlib `DirectedSystem` instances, both on vertex carriers
and on ACTUAL finite raw automorphism subgroups.

We use the explicit quotient direct limit (not an abstract unproved
limit). Each old finite carrier injects into the vertex limit, and
each old finite group injects into the group limit. These two limits
are built using their own compatible maps, with no unsupported
claim yet of a global action of the limit group on the limit vertices,
nor of Fraisse homogeneity/density.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Actual vertex maps of the tower, preserving and reflecting all
old E and ordered R_c predicates. -/
def vertexTransition (T : FiniteSafeRawPairTower d V)
    (i j : ℕ) (h : i ≤ j) : V i → V j :=
  (T.between i j h).vertex

/-- Actual finite automorphism-group homomorphisms from the tower.
Every map is injective and strictly intertwines vertex transitions. -/
def groupTransition (T : FiniteSafeRawPairTower d V)
    (i j : ℕ) (h : i ≤ j) :
    (T.stage i).subgroup →* (T.stage j).subgroup :=
  (T.between i j h).groupMap

instance vertexDirectedSystem (T : FiniteSafeRawPairTower d V) :
    DirectedSystem V (fun ⦃i j⦄ (h : i ≤ j) => T.vertexTransition i j h) where
  map_self := by
    intro i x
    exact T.between_self_vertex i x
  map_map := by
    intro k j i hij hjk x
    exact (T.between_trans_vertex i j k hij hjk x).symm

instance groupDirectedSystem (T : FiniteSafeRawPairTower d V) :
    DirectedSystem (fun i : ℕ => (T.stage i).subgroup)
      (fun ⦃i j⦄ (h : i ≤ j) => T.groupTransition i j h) where
  map_self := by
    intro i x
    exact T.between_self_group i x
  map_map := by
    intro k j i hij hjk x
    exact (T.between_trans_group i j k hij hjk x).symm

/-- Actual quotient direct limit of finite original-language vertices.
Relations on the limit will be transported separately. -/
abbrev VertexLimit (T : FiniteSafeRawPairTower d V) :=
  DirectLimit V T.vertexTransition

/-- Actual group direct limit of finite safe automorphism subgroups.
The standard mathlib algebraic colimit carries a genuine Group
instance, since the transitions are monoid homomorphisms. -/
abbrev GroupLimit (T : FiniteSafeRawPairTower d V) :=
  DirectLimit (fun i : ℕ => (T.stage i).subgroup) T.groupTransition

/-- Canonical inclusion of old vertices into the quotient limit. -/
def vertexOf (T : FiniteSafeRawPairTower d V) (i : ℕ) :
    V i → T.VertexLimit :=
  fun x => ⟦⟨i, x⟩⟧

/-- Canonical inclusion of an actual old finite acting group. -/
def groupOf (T : FiniteSafeRawPairTower d V) (i : ℕ) :
    (T.stage i).subgroup → T.GroupLimit :=
  fun h => ⟦⟨i, h⟩⟧

/-- Every finite raw vertex carrier embeds INJECTIVELY in the
direct-limit carrier: no two distinct old points are identified. -/
theorem vertexOf_injective (T : FiniteSafeRawPairTower d V) (i : ℕ) :
    Function.Injective (T.vertexOf i) := by
  exact DirectLimit.mk_injective
    (f := T.vertexTransition)
    (fun a b hab => (T.between a b hab).vertex_injective) i

/-- Every finite safe group injects into the algebraic group limit:
the direct limit does not collapse any nontrivial old automorphism. -/
theorem groupOf_injective (T : FiniteSafeRawPairTower d V) (i : ℕ) :
    Function.Injective (T.groupOf i) := by
  exact DirectLimit.mk_injective
    (f := T.groupTransition)
    (fun a b hab => (T.between a b hab).group_injective) i

/-- Canonical vertex inclusions commute with every finite-stage map. -/
theorem vertexOf_transition (T : FiniteSafeRawPairTower d V)
    (i j : ℕ) (hij : i ≤ j) (x : V i) :
    T.vertexOf j (T.vertexTransition i j hij x) =
      T.vertexOf i x := by
  exact DirectLimit.mk_apply
    (f := T.vertexTransition) i j x hij

/-- Canonical finite-group inclusions commute with every finite-stage
group homomorphism, on the same literal group element. -/
theorem groupOf_transition (T : FiniteSafeRawPairTower d V)
    (i j : ℕ) (hij : i ≤ j) (g : (T.stage i).subgroup) :
    T.groupOf j (T.groupTransition i j hij g) =
      T.groupOf i g := by
  exact DirectLimit.mk_apply
    (f := T.groupTransition) i j g hij

end FiniteSafeRawPairTower
end SemigenericEPPA
