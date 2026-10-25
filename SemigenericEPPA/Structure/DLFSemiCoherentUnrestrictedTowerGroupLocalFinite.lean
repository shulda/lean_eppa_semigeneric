import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerDirectedLimits
import SemigenericEPPA.Algebra.DLFAscendingFiniteSubgroups

/-!
# Unrestricted semi-coherent action-tower colimit: GroupLocalFinite

Port of the verified original-raw finite stage/group-limit theorem
from finite SAFE action pairs to arbitrary finite group-action pairs.
Only injective original E/R_c embeddings and strict equivariant
finite group homomorphisms are required. No local safety hypothesis.
The next modules will construct the actual limit action and density.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G] {C : Type v} [Finite C]
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- Each genuine finite automorphism subgroup embeds homomorphically
in the actual algebraic directed-limit group. -/
noncomputable def groupOfHom (T : FiniteRawActionPairTower d V) (n : ℕ) :
    (T.stage n).subgroup →* T.GroupLimit where
  toFun := T.groupOf n
  map_one' := by
    exact (DirectLimit.one_def
      (f := T.groupTransition) n).symm
  map_mul' x y := by
    exact (DirectLimit.mul_def
      (f := T.groupTransition) n x y).symm

/-- Actual finite subgroup at level n, inside the ONE group limit. -/
noncomputable def stageImage (T : FiniteRawActionPairTower d V) (n : ℕ) :
    Subgroup T.GroupLimit :=
  (T.groupOfHom n).range

/-- Every stage-image subgroup is finite. -/
theorem finite_stageImage (T : FiniteRawActionPairTower d V) (n : ℕ) :
    Finite (T.stageImage n) := by
  classical
  letI : Finite (T.stage n).raw.fullRawAutGroup :=
    (T.stage n).raw.finite_fullRawAutGroup
  letI : Finite (T.stage n).subgroup := inferInstance
  exact Finite.of_surjective
    (fun h : (T.stage n).subgroup =>
      (⟨T.groupOfHom n h, ⟨h, rfl⟩⟩ : T.stageImage n))
    (by
      intro y
      obtain ⟨h, hh⟩ := y.property
      refine ⟨h, ?_⟩
      apply Subtype.ext
      exact hh)

/-- Stage images form one monotone ascending chain of ACTUAL subgroups
of the SAME genuine group direct limit. -/
theorem stageImage_monotone (T : FiniteRawActionPairTower d V) :
    Monotone T.stageImage := by
  intro n m hnm g hg
  obtain ⟨h, hh⟩ := hg
  refine ⟨T.groupTransition n m hnm h, ?_⟩
  exact (T.groupOf_transition n m hnm h).trans hh

/-- Every element of the quotient group limit already comes from a
finite actual subgroup at some stage. -/
theorem stageImage_covers (T : FiniteRawActionPairTower d V) :
    ∀ g : T.GroupLimit, ∃ n : ℕ, g ∈ T.stageImage n := by
  intro g
  obtain ⟨n, h, hh⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  exact ⟨n, ⟨h, hh.symm⟩⟩

/-- The group directed limit of ANY tower of finite safe original
raw pairs is locally finite, in the genuine finitely generated
subgroup sense. This already constructs the locally finite
algebraic candidate for DLF, independently of Fraisse density. -/
theorem groupLimit_locallyFinite (T : FiniteRawActionPairTower d V) :
    EveryFinitelyGeneratedSubgroupFinite T.GroupLimit :=
  locallyFinite_of_ascendingFiniteSubgroups
    T.stageImage
    T.stageImage_monotone
    T.finite_stageImage
    T.stageImage_covers

end FiniteRawActionPairTower
end SemigenericEPPA
