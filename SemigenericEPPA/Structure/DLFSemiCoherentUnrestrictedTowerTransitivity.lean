import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerCoherence

/-!
# Unrestricted semi-coherent action tower: strict transitivity

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

/-- Strict transitivity of finite raw vertex embeddings in any
successor tower of genuine safe pairs. -/
theorem between_trans_vertex
    (T : FiniteRawActionPairTower d V)
    (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) (x : V n) :
    (T.between n k (hnm.trans hmk)).vertex x =
      (T.between m k hmk).vertex ((T.between n m hnm).vertex x) := by
  induction k, hmk using Nat.le_induction with
  | base =>
      exact (T.between_self_vertex m
        ((T.between n m hnm).vertex x)).symm
  | succ k hmk ih =>
      calc
        (T.between n (k + 1)
            (hnm.trans (Nat.le_succ_of_le hmk))).vertex x =
            (T.step k).vertex ((T.between n k
              (hnm.trans hmk)).vertex x) :=
          T.between_succ_vertex n k (hnm.trans hmk) x
        _ = (T.step k).vertex
              ((T.between m k hmk).vertex
                ((T.between n m hnm).vertex x)) :=
          congrArg (T.step k).vertex ih
        _ = (T.between m (k + 1)
              (Nat.le_succ_of_le hmk)).vertex
                ((T.between n m hnm).vertex x) :=
          (T.between_succ_vertex m k hmk
              ((T.between n m hnm).vertex x)).symm

/-- Strict transitivity of the corresponding injective finite
automorphism-group homomorphisms. -/
theorem between_trans_group
    (T : FiniteRawActionPairTower d V)
    (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k)
    (h : (T.stage n).subgroup) :
    (T.between n k (hnm.trans hmk)).groupMap h =
      (T.between m k hmk).groupMap
        ((T.between n m hnm).groupMap h) := by
  induction k, hmk using Nat.le_induction with
  | base =>
      exact (T.between_self_group m
        ((T.between n m hnm).groupMap h)).symm
  | succ k hmk ih =>
      calc
        (T.between n (k + 1)
            (hnm.trans (Nat.le_succ_of_le hmk))).groupMap h =
            (T.step k).groupMap ((T.between n k
              (hnm.trans hmk)).groupMap h) :=
          T.between_succ_group n k (hnm.trans hmk) h
        _ = (T.step k).groupMap
              ((T.between m k hmk).groupMap
                ((T.between n m hnm).groupMap h)) :=
          congrArg (T.step k).groupMap ih
        _ = (T.between m (k + 1)
              (Nat.le_succ_of_le hmk)).groupMap
                ((T.between n m hnm).groupMap h) :=
          (T.between_succ_group m k hmk
              ((T.between n m hnm).groupMap h)).symm


end FiniteRawActionPairTower
end SemigenericEPPA
