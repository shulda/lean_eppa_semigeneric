import SemigenericEPPA.Structure.DLFSafePairTowerCoherence

/-!
# True transitivity of finite safe-pair transition maps

Every tower step embeds not only the original raw E and R_c relations,
but also the finite acting subgroup, injectively and equivariantly.
For all n ≤ m ≤ k, the n→k vertex map and the n→k group map equal
their n→m→k composites POINTWISE, with no arbitrary isomorphism.
These are the coherence identities needed for directed colimits of
vertices and actual acting groups.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Strict transitivity of finite raw vertex embeddings in any
successor tower of genuine safe pairs. -/
theorem between_trans_vertex
    (T : FiniteSafeRawPairTower d V)
    (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) (x : V n) :
    (T.between n k (hnm.trans hmk)).vertex x =
      (T.between m k hmk).vertex ((T.between n m hnm).vertex x) := by
  induction k, hmk using Nat.le_induction with
  | base =>
      simpa only [between_self_vertex]
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
    (T : FiniteSafeRawPairTower d V)
    (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k)
    (h : (T.stage n).subgroup) :
    (T.between n k (hnm.trans hmk)).groupMap h =
      (T.between m k hmk).groupMap
        ((T.between n m hnm).groupMap h) := by
  induction k, hmk using Nat.le_induction with
  | base =>
      simpa only [between_self_group]
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

end FiniteSafeRawPairTower
end SemigenericEPPA
