import SemigenericEPPA.Structure.DLFSafePairTowerLimitAutHom
import SemigenericEPPA.Structure.DLFSafePairTowerConditionalDensity
import SemigenericEPPA.Structure.DLFSafePairTowerGroupLocalFinite
import SemigenericEPPA.Algebra.DLFDenseLocallyFiniteTowerCriterion

/-!
# A safe-pair tower with next-stage connectors gives ACTUAL DLF automorphisms

This is the final conditional positive algebraic limit bridge.

Any genuine finite-safe-pair tower with the exact next-stage
partial raw automorphism extension property constructs a single
locally finite subgroup of the ACTUAL original-language automorphism
group of its true quotient-limit raw rectangle, dense on finite
point restrictions.

The finite subgroups at stage n are the images of genuine stage
automorphism groups inside the limit's literal permutation group.
Their monotonicity and finiteness follow from the certified group
colimit. Exact approximation of arbitrary limit automorphisms on
finite vertex sets follows from the certified next-stage connector
lemma. The existing abstract ascending finite subgroup theorem
then produces a locally finite subgroup with this density property.

Crucially, the only UNSOLVED positive existence assumption is now
a suitable AGE-COFINAL countable tower with those connectors.
Neither its existence nor identification with the full Fraïssé
limit is asserted here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- A genuine tower whose next groups extend all finite-stage partial
raw automorphisms yields a dense locally finite subgroup of the
ACTUAL full original E/R_c automorphism group of its infinite
raw-rectangle colimit. Density is exact agreement on every finite
set of vertices, the permutation-topological criterion. -/
theorem exists_actualDenseLocallyFiniteSubgroup_of_connectors
    (T : FiniteSafeRawPairTower d V)
    (hConn : T.HasNextStageRawConnectors) :
    ∃ L : Subgroup (Equiv.Perm T.VertexLimit),
      L ≤ T.limitRawPresentation.fullRawAutGroup ∧
      DenseByFiniteRestrictions T.limitRawPresentation.fullRawAutGroup L ∧
      EveryFinitelyGeneratedSubgroupFinite L := by
  classical
  let A : Subgroup (Equiv.Perm T.VertexLimit) :=
    T.limitRawPresentation.fullRawAutGroup
  let rho : T.GroupLimit →* Equiv.Perm T.VertexLimit :=
    A.subtype.comp T.limitRawAutHom
  let K : ℕ → Subgroup (Equiv.Perm T.VertexLimit) :=
    fun n => (T.stageImage n).map rho
  have hMono : Monotone K := by
    intro n m hnm f hf
    obtain ⟨g, hg, hEq⟩ := hf
    exact ⟨g, T.stageImage_monotone hnm hg, hEq⟩
  have hFinite : ∀ n, Finite (K n) := by
    intro n
    letI : Finite (T.stageImage n) := T.finite_stageImage n
    have hSurj : Function.Surjective
        (fun g : T.stageImage n =>
          (⟨rho g.val, ⟨g.val, g.property, rfl⟩⟩ : K n)) := by
      intro z
      obtain ⟨g, hg, heq⟩ := z.property
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      exact heq
    exact Finite.of_surjective _ hSurj
  have hInside : ∀ n, K n ≤ A := by
    intro n f hf
    obtain ⟨g, _hg, heq⟩ := hf
    have hRaw : rho g ∈ A :=
      (T.limitRawAutHom g).property
    exact heq ▸ hRaw
  have hApprox : ∀ (a : A) (F : Finset T.VertexLimit),
      ∃ n : ℕ, ∃ k : K n,
        ∀ x : T.VertexLimit, x ∈ F → k.val x = a.val x := by
    intro a F
    have hPart : ∀ x y : T.VertexLimit,
        T.limitPart (a.val x) (a.val y) ↔ T.limitPart x y := by
      intro x y
      exact T.limitRawPresentation.fullRawAutGroup_part a x y
    have hColour : ∀ x y : T.VertexLimit,
        T.limitColour (a.val x) (a.val y) = T.limitColour x y := by
      intro x y
      exact T.limitRawPresentation.fullRawAutGroup_colour a x y
    obtain ⟨g, hg⟩ :=
      T.finiteRestrictionApprox_of_nextStageRawConnectors
        hConn a.val hPart hColour F
    obtain ⟨n, hn⟩ := T.stageImage_covers g
    refine ⟨n, ⟨rho g, ⟨g, hn, rfl⟩⟩, ?_⟩
    intro x hx
    change T.limitAct g x = a.val x
    exact hg x hx
  exact exists_locallyFinite_denseByFiniteRestrictions_of_tower
    A K hMono hFinite hInside hApprox

end FiniteSafeRawPairTower
end SemigenericEPPA
