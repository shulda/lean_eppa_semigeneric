import SemigenericEPPA.Structure.DLFSafePairTowerDirectedLimits
import SemigenericEPPA.Algebra.DLFAscendingFiniteSubgroups

/-!
# The actual directed-limit finite-group tower is locally finite

Starting with a tower of genuine finite original-language safe pairs,
we already have strict injective transition group homomorphisms and
the explicit quotient directed group limit. We now prove that its
ascending images are finite subgroups covering the entire limit.
Hence every finitely generated subgroup of the ACTUAL GROUP LIMIT
is finite, applying the previously certified algebraic lemma.

This does NOT yet assert the group acts on the vertex limit or
that its image is dense in a Fraisse automorphism group.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- Each genuine finite automorphism subgroup embeds homomorphically
in the actual algebraic directed-limit group. -/
def groupOfHom (T : FiniteSafeRawPairTower d V) (n : ℕ) :
    (T.stage n).subgroup →* T.GroupLimit where
  toFun := T.groupOf n
  map_one' := by
    exact (DirectLimit.one_def
      (f := T.groupTransition) n).symm
  map_mul' x y := by
    exact (DirectLimit.mul_def
      (f := T.groupTransition) n x y).symm

/-- Actual finite subgroup at level n, inside the ONE group limit. -/
def stageImage (T : FiniteSafeRawPairTower d V) (n : ℕ) :
    Subgroup T.GroupLimit :=
  (T.groupOfHom n).range

/-- Every stage-image subgroup is finite. -/
theorem finite_stageImage (T : FiniteSafeRawPairTower d V) (n : ℕ) :
    Finite (T.stageImage n) := by
  classical
  letI : Finite (T.stage n).subgroup :=
    (T.stage n).finite_subgroup
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
theorem stageImage_monotone (T : FiniteSafeRawPairTower d V) :
    Monotone T.stageImage := by
  intro n m hnm g hg
  obtain ⟨h, hh⟩ := hg
  refine ⟨T.groupTransition n m hnm h, ?_⟩
  exact (T.groupOf_transition n m hnm h).trans hh

/-- Every element of the quotient group limit already comes from a
finite actual subgroup at some stage. -/
theorem stageImage_covers (T : FiniteSafeRawPairTower d V) :
    ∀ g : T.GroupLimit, ∃ n : ℕ, g ∈ T.stageImage n := by
  intro g
  obtain ⟨n, h, hh⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  exact ⟨n, ⟨h, hh.symm⟩⟩

/-- The group directed limit of ANY tower of finite safe original
raw pairs is locally finite, in the genuine finitely generated
subgroup sense. This already constructs the locally finite
algebraic candidate for DLF, independently of Fraisse density. -/
theorem groupLimit_locallyFinite (T : FiniteSafeRawPairTower d V) :
    EveryFinitelyGeneratedSubgroupFinite T.GroupLimit :=
  locallyFinite_of_ascendingFiniteSubgroups
    T.stageImage
    T.stageImage_monotone
    T.finite_stageImage
    T.stageImage_covers

end FiniteSafeRawPairTower
end SemigenericEPPA
