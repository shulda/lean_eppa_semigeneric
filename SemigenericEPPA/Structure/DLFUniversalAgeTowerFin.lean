import SemigenericEPPA.Structure.DLFCountableRawAgeSchedule
import SemigenericEPPA.Structure.DLFSafePairTowerActualDLFCriterion
import SemigenericEPPA.Structure.DLFSafePairTowerLimitHomogeneity

/-!
# An actual safe connector tower whose limit contains EVERY finite raw rectangle

All the necessary ingredients now exist:

* One complete good affine congruence orbit gives a strictly
  equivariant finite safe successor with arbitrary prescribed
  age target AND all old partial raw automorphism connectors.
* Classical recursion builds an actual countable tower for
  any schedule of finite original R1–R3 raw presentations.
* Since C is finite, the canonical finite carriers Fin n have
  finitely many raw E/R_c presentations for each n, hence
  there is a surjective ℕ enumeration of those presentations.
* Every scheduled old target embeds inducedly in the true quotient
  colimit; the same tower has all connectors. Existing CI-certified
  theorems then supply original-language ultrahomogeneity and one
  dense locally finite subgroup of its ACTUAL automorphism group.

We first state the full age-universality on all canonical finite
carriers Fin n. Every arbitrary finite carrier is equivalent to
one Fin n; that final normalization may be exported separately.

No infinite-model or Fraïssé existence axiom is assumed.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- The chosen canonical schedule and any age-target tower
give an induced embedding of every Fin n raw rectangle into
the genuine original-language infinite quotient limit. -/
theorem universalAgeFin_of_canonicalSchedule
    {V : ℕ → Type (max u v)}
    [∀ n, Finite (V n)]
    (T : FiniteSafeRawPairTower d V)
    (hTargets : ∀ i : ℕ,
      ∃ q : (canonicalFiniteRawTargets (d := d) i).carrier → V (i+1),
        Function.Injective q ∧
        (∀ x y : (canonicalFiniteRawTargets (d := d) i).carrier,
          (T.stage (i+1)).raw.part (q x) (q y) ↔
            (canonicalFiniteRawTargets (d := d) i).raw.part x y) ∧
        (∀ x y : (canonicalFiniteRawTargets (d := d) i).carrier,
          (T.stage (i+1)).raw.colour (q x) (q y) =
            (canonicalFiniteRawTargets (d := d) i).raw.colour x y)) :
    ∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → T.VertexLimit,
        Function.Injective e ∧
        (∀ x y : Fin n,
          T.limitRawPresentation.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : Fin n,
          T.limitRawPresentation.colour (e x) (e y) =
            P.colour x y) := by
  intro n P
  obtain ⟨i, hi⟩ :=
    canonicalFiniteRawSchedule_surjective (d := d) ⟨n, P⟩
  have hScheduled :=
    safeTower_ageSchedule_embedsInLimit
      T (canonicalFiniteRawTargets (d := d)) hTargets i
  simp only [canonicalFiniteRawTargets, hi] at hScheduled
  obtain ⟨e, he, hp, hc⟩ := hScheduled
  refine ⟨fun x => e (ULift.up x), he.comp ULift.up_injective, ?_, ?_⟩
  · intro x y
    simpa only [RawRectanglePresentation.pullbackRaw] using
      hp (ULift.up x) (ULift.up y)
  · intro x y
    simpa only [RawRectanglePresentation.pullbackRaw] using
      hc (ULift.up x) (ULift.up y)

/-- Under ONE complete good affine orbit, from any initial finite
safe original raw pair there exists a GENUINE countable chain whose
limit is original-language homogeneous, contains every finite
raw rectangle on Fin n, and whose actual automorphism group has a
dense locally finite subgroup.

The witness is NOT an abstract postulated homogeneous model: it is
the true quotient colimit of the explicit finite safe-pair tower. -/
theorem exists_universalHomogeneousDLFTower_onFin
    (A₀ : FiniteSafePairState d)
    (hOrbit : d.HasCompleteGoodOrbit) :
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
    exists_safeTower_realizingAgeSchedule A₀ targets hOrbit
  letI : ∀ n, Finite (V n) := hV
  refine ⟨V, hV, T, hConn, hInitial, ?_, ?_⟩
  · exact universalAgeFin_of_canonicalSchedule T hTargets
  · exact T.exists_actualDenseLocallyFiniteSubgroup_of_connectors hConn

end SemigenericEPPA
