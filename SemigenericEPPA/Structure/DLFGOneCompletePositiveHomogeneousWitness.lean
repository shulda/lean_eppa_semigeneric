import SemigenericEPPA.Structure.DLFGOneAgeScheduledSafeTower
import SemigenericEPPA.Structure.DLFCompletePositiveHomogeneousWitness

/-!
# Full exceptional G=1 positive DLF theorem without any complete good orbit

The certified canonical finite raw-age schedule and all existing
quotient-limit group/automorphism/homogeneity/countability theorems
depend only on a genuine age-scheduled finite safe-pair tower with
all next-stage partial original-language connectors.

For subsingleton effective group G, such a tower follows from the
G=1 finite relative safe subgroup EPPA construction without any
HasCompleteGoodOrbit or self-reversing raw colour. This assembles:

* a countable true quotient-limit original E/R_c structure;
* induced embeddings of EVERY finite original raw rectangle on
  arbitrary finite carriers, via the canonical Fin schedule;
* extension of EVERY finite original-language partial automorphism
  to an actual full automorphism of the limit;
* a dense locally finite subgroup of the actual raw automorphism group.

This theorem is the exceptional positive DLF sufficiency branch.
It does not prove the converse for nontrivial effective groups.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- G=1 tower with the full canonical finite original raw age,
all connectors, and a genuine dense locally finite Aut subgroup. -/
theorem exists_gOne_universalHomogeneousDLFTower_onFin
    (A₀ : FiniteSafePairState d) :
    ∃ (V : ℕ → Type (max u v))
      (hV : ∀ n, Finite (V n)),
      letI : ∀ n, Finite (V n) := hV
      ∃ T : FiniteSafeRawPairTower d V,
        T.HasNextStageRawConnectors ∧
        V 0 = A₀.carrier ∧
        (∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
          ∃ e : Fin n → T.VertexLimit,
            Function.Injective e ∧
            (∀ x y : Fin n,
              T.limitRawPresentation.part (e x) (e y) ↔ P.part x y) ∧
            (∀ x y : Fin n,
              T.limitRawPresentation.colour (e x) (e y) = P.colour x y)) ∧
        (∃ L : Subgroup (Equiv.Perm T.VertexLimit),
          L ≤ T.limitRawPresentation.fullRawAutGroup ∧
          DenseByFiniteRestrictions T.limitRawPresentation.fullRawAutGroup L ∧
          EveryFinitelyGeneratedSubgroupFinite L) := by
  classical
  let targets : ℕ → FiniteRawAgeTarget d :=
    canonicalFiniteRawTargets (d := d)
  obtain ⟨V, hV, T, hConn, hInitial, hTargets⟩ :=
    exists_gOne_safeTower_realizingAgeSchedule A₀ targets
  letI : ∀ n, Finite (V n) := hV
  refine ⟨V, hV, T, hConn, hInitial, ?_, ?_⟩
  · exact universalAgeFin_of_canonicalSchedule T hTargets
  · exact T.exists_actualDenseLocallyFiniteSubgroup_of_connectors hConn


/-- Exceptional G=1 positive DLF classification branch:
the full countable homogeneous original-language witness exists
without any good-orbit condition. -/
theorem RawDatum.exists_countableHomogeneousDLF_of_subsingleton
    (d : RawDatum G C) :
    ∃ (V : ℕ → Type (max u v))
      (hV : ∀ n, Finite (V n)),
      letI : ∀ n, Finite (V n) := hV
      ∃ T : FiniteSafeRawPairTower d V,
        Countable T.VertexLimit ∧
        (∀ (W : Type w) [Fintype W]
          (P : RawRectanglePresentation d W),
          ∃ e : W → T.VertexLimit,
            Function.Injective e ∧
            (∀ x y : W,
              T.limitRawPresentation.part (e x) (e y) ↔ P.part x y) ∧
            (∀ x y : W,
              T.limitRawPresentation.colour (e x) (e y) = P.colour x y)) ∧
        (∀ (F : Finset T.VertexLimit) (p : F → T.VertexLimit),
          Function.Injective p →
          (∀ x y : F,
            T.limitRawPresentation.part (p x) (p y) ↔
              T.limitRawPresentation.part x.val y.val) →
          (∀ x y : F,
            T.limitRawPresentation.colour (p x) (p y) =
              T.limitRawPresentation.colour x.val y.val) →
          ∃ a : T.limitRawPresentation.fullRawAutGroup,
            ∀ x : F, a.val x.val = p x) ∧
        (∃ L : Subgroup (Equiv.Perm T.VertexLimit),
          L ≤ T.limitRawPresentation.fullRawAutGroup ∧
          DenseByFiniteRestrictions T.limitRawPresentation.fullRawAutGroup L ∧
          EveryFinitelyGeneratedSubgroupFinite L) := by
  classical
  let A₀ : FiniteSafePairState d := {
    carrier := ULift.{max u v} (Fin 0)
    finite_carrier := inferInstance
    pair := ((emptyFiniteRaw (d := d)).pullbackRaw ULift.down).trivialSafePair
  }
  obtain ⟨V, hV, T, hConn, _hOld, hFin, hDLF⟩ :=
    exists_gOne_universalHomogeneousDLFTower_onFin A₀
  letI : ∀ n, Finite (V n) := hV
  refine ⟨V, hV, T, T.countable_vertexLimit, ?_, ?_, hDLF⟩
  · exact T.limitRawPresentation.inducedFiniteAge_of_canonicalFinAge hFin
  · intro F p hp hPart hColour
    exact T.finiteRawPartialMap_extends_on_limit
      hConn F p hp hPart hColour


end SemigenericEPPA
