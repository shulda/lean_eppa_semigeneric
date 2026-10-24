import SemigenericEPPA.Structure.DLFSafePairTower

/-!
# Coherence of every finite-stage safe-pair transition

The raw/vertex and group maps from the n-th finite safe pair to any
later m-th pair are constructed by recursion through successive
strictly equivariant maps. Here we certify that their action does
not depend on a choice of intermediate stage: the structure maps
and group maps compose exactly, not merely up to isomorphism.

These are the compatibility identities required to construct the
honest directed colimits of the vertex structures and finite groups.
No countable colimit or Fraïssé theorem is claimed in this file.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- The stage transition on vertices at a successor index is the
old transition followed by the next one-step embedding. -/
theorem between_succ_vertex
    (T : FiniteSafeRawPairTower d V)
    (n m : ℕ) (hnm : n ≤ m) (x : V n) :
    (T.between n (m + 1) (Nat.le_succ_of_le hnm)).vertex x =
      (T.step m).vertex ((T.between n m hnm).vertex x) := by
  unfold between
  rw [Nat.leRecOn_succ hnm]
  rfl

/-- Identical successor law for the finite acting group. -/
theorem between_succ_group
    (T : FiniteSafeRawPairTower d V)
    (n m : ℕ) (hnm : n ≤ m) (h : (T.stage n).subgroup) :
    (T.between n (m + 1) (Nat.le_succ_of_le hnm)).groupMap h =
      (T.step m).groupMap ((T.between n m hnm).groupMap h) := by
  unfold between
  rw [Nat.leRecOn_succ hnm]
  rfl

end FiniteSafeRawPairTower
end SemigenericEPPA
