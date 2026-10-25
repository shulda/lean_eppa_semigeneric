import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedFiniteTower

/-!
# Unrestricted semi-coherent action tower: successor coherence

Exact replay of the certified safe-tower finite-stage theorem with
an ARBITRARY selected original-raw finite group-action pair.
The proofs require only strict injective equivariant embeddings.
No assumption of local involution safety appears in the statements.

This is a step toward proving that the genuine unrestricted
semi-coherent extension property gives a dense locally finite
group, without applying Sagi's general theorem as an axiom.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v} [Finite C]
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- The stage transition on vertices at a successor index is the
old transition followed by the next one-step embedding. -/
theorem between_succ_vertex
    (T : FiniteRawActionPairTower d V)
    (n m : ℕ) (hnm : n ≤ m) (x : V n) :
    (T.between n (m + 1) (Nat.le_succ_of_le hnm)).vertex x =
      (T.step m).vertex ((T.between n m hnm).vertex x) := by
  unfold between
  rw [Nat.leRecOn_succ hnm]
  rfl

/-- Identical successor law for the finite acting group. -/
theorem between_succ_group
    (T : FiniteRawActionPairTower d V)
    (n m : ℕ) (hnm : n ≤ m) (h : (T.stage n).subgroup) :
    (T.between n (m + 1) (Nat.le_succ_of_le hnm)).groupMap h =
      (T.step m).groupMap ((T.between n m hnm).groupMap h) := by
  unfold between
  rw [Nat.leRecOn_succ hnm]
  rfl


end FiniteRawActionPairTower
end SemigenericEPPA
