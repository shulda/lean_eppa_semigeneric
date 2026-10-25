import SemigenericEPPA.Structure.DLFNegativeCompleteNecessity
import SemigenericEPPA.Structure.DLFGOneCompletePositiveHomogeneousWitness
import SemigenericEPPA.Structure.DLFCompletePositiveHomogeneousWitness

/-!
# Public DLF classification: exact full-age homogeneous original-language witnesses

The positive finite-safe-pair tower construction is established
under one complete good affine orbit, and independently for a
subsingleton effective group G even without a good raw colour.

The separate negative original-language proof establishes that,
for nontrivial G, a homogeneous raw rectangle with its FULL finite
R1--R3 age and a dense locally finite subgroup of genuine raw
automorphisms must have a complete good affine orbit.

The single public predicate below packages the precise homogeneous
countable DLF model, in the actual original E/R_c language with all
finite canonical raw rectangles embedded inducedly. The full
classification is exactly:

    G subsingleton OR d.HasCompleteGoodOrbit.

This module depends on the new negative proof and is a proposed
final integration theorem until the entire dependency chain passes
the full Lean build and allowed-axiom audit.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- The original raw age has a genuine countable ultrahomogeneous
structure whose actual original-language automorphism group
contains a dense locally finite subgroup.

The model and subgroup are witnesses, not abstract axioms. -/
def HasCountableHomogeneousDLF (d : RawDatum G C) : Prop :=
  ∃ (V : Type (max u v))
    (M : RawRectanglePresentation d V),
    Countable V ∧
    (∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → V,
        Function.Injective e ∧
        (∀ x y : Fin n,
          M.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : Fin n,
          M.colour (e x) (e y) = P.colour x y)) ∧
    (∀ (F : Finset V) (p : F → V),
      Function.Injective p →
      (∀ x y : F,
        M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : F,
        M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ a : M.fullRawAutGroup,
        ∀ x : F, a.val x.val = p x) ∧
    (∃ L : Subgroup (Equiv.Perm V),
      L ≤ M.fullRawAutGroup ∧
      DenseByFiniteRestrictions M.fullRawAutGroup L ∧
      EveryFinitelyGeneratedSubgroupFinite L)

/-- A complete good affine orbit constructs the full actual raw
homogeneous countable DLF witness. -/
theorem hasCountableHomogeneousDLF_of_completeGoodOrbit
    (d : RawDatum G C) (hOrbit : d.HasCompleteGoodOrbit) :
    d.HasCountableHomogeneousDLF := by
  classical
  obtain ⟨V, hV, T, hCount, hAge, hHom, hDLF⟩ :=
    d.exists_countableHomogeneousDLF_of_completeGoodOrbit.{u, v, 0} hOrbit
  letI : ∀ n, Finite (V n) := hV
  refine ⟨T.VertexLimit, T.limitRawPresentation,
    hCount, ?_, hHom, hDLF⟩
  intro n P
  exact hAge (Fin n) P

/-- The trivial effective-group case needs no good raw colour. -/
theorem hasCountableHomogeneousDLF_of_subsingleton
    (d : RawDatum G C) [Subsingleton G] :
    d.HasCountableHomogeneousDLF := by
  classical
  obtain ⟨V, hV, T, hCount, hAge, hHom, hDLF⟩ :=
    d.exists_countableHomogeneousDLF_of_subsingleton.{u, v, 0}
  letI : ∀ n, Finite (V n) := hV
  refine ⟨T.VertexLimit, T.limitRawPresentation,
    hCount, ?_, hHom, hDLF⟩
  intro n P
  exact hAge (Fin n) P

/-- For nontrivial effective G the only possible full original
homogeneous DLF witnesses have one complete good affine orbit. -/
theorem completeGoodOrbit_of_hasCountableHomogeneousDLF
    (d : RawDatum G C) [Nontrivial G]
    (h : d.HasCountableHomogeneousDLF) :
    d.HasCompleteGoodOrbit := by
  obtain ⟨V, M, _hCount, hAge, hHom, hDLF⟩ := h
  exact M.completeGoodOrbit_of_denseLocallyFinite hAge hHom hDLF

/-- Complete DLF classification in the genuine original-language
homogeneous age, with the exceptional G=1 branch separated from
the complete-good-orbit branch. -/
theorem hasCountableHomogeneousDLF_iff
    (d : RawDatum G C) :
    d.HasCountableHomogeneousDLF ↔
      Subsingleton G ∨ d.HasCompleteGoodOrbit := by
  classical
  constructor
  · intro h
    by_cases hSub : Subsingleton G
    · exact Or.inl hSub
    · have hDiff : ∃ x y : G, x ≠ y := by
        by_contra hn
        apply hSub
        constructor
        intro x y
        by_contra hxy
        exact hn ⟨x, y, hxy⟩
      letI : Nontrivial G := ⟨hDiff⟩
      exact Or.inr (d.completeGoodOrbit_of_hasCountableHomogeneousDLF h)
  · rintro (hSub | hOrbit)
    · letI : Subsingleton G := hSub
      exact d.hasCountableHomogeneousDLF_of_subsingleton
    · exact d.hasCountableHomogeneousDLF_of_completeGoodOrbit hOrbit

end RawDatum
end SemigenericEPPA
