import SemigenericEPPA.Structure.DLFNegativeCompleteNecessity
import SemigenericEPPA.Structure.DLFCompletePositiveHomogeneousWitness
import SemigenericEPPA.Structure.DLFGOneCompletePositiveHomogeneousWitness

/-!
# Complete DLF classification in the original semigeneric R1–R3 language

The exact original-language target is the existence of a countable
homogeneous raw rectangle carrying its FULL finite R1–R3 age and
admitting a dense locally finite subgroup of its ACTUAL
E- and all R_c-preserving automorphism group.

We use the canonical Fin n presentation of full finite age: the
certified normalization theorem transports this to every finite
carrier without weakening or relabelling any original raw colour.

The two positive branches are independently certified:
* Subsingleton G, with NO complete-good-orbit assumption;
* one complete good affine congruence orbit for arbitrary finite G.

The negative branch forbids DLF for nontrivial G when no such
complete good orbit exists, by exact finite relative row gadgets,
the absence of all involutions and the genuine two-cycle parity
argument. No semi-coherent-to-DLF bridge, transfinite existence
axiom, false global saturation condition or external homogeneous
model is assumed.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- The literal original-language countable homogeneous DLF
property. Canonical finite-age universality is equivalent to
universality on all finite carriers by the certified exact
finite normalization; fullRawAutGroup preserves E and EVERY
ordered raw Option-C colour. -/
def HasCountableHomogeneousDLF (d : RawDatum G C) : Prop :=
  ∃ (X : Type (max u v)) (M : RawRectanglePresentation d X),
    Countable X ∧
    (∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → X,
        Function.Injective e ∧
        (∀ x y : Fin n,
          M.part (e x) (e y) ↔ P.part x y) ∧
        (∀ x y : Fin n,
          M.colour (e x) (e y) = P.colour x y)) ∧
    (∀ (F : Finset X) (p : F → X),
      Function.Injective p →
      (∀ x y : F, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : F, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ a : M.fullRawAutGroup,
        ∀ x : F, a.val x.val = p x) ∧
    (∃ L : Subgroup (Equiv.Perm X),
      L ≤ M.fullRawAutGroup ∧
      DenseByFiniteRestrictions M.fullRawAutGroup L ∧
      EveryFinitelyGeneratedSubgroupFinite L)

/-- Sufficiency of ONE complete good orbit, using the actual
constructed safe-pair quotient limit and its genuine raw Aut group. -/
theorem hasCountableHomogeneousDLF_of_completeGoodOrbit
    (d : RawDatum G C)
    (hOrbit : d.HasCompleteGoodOrbit) :
    d.HasCountableHomogeneousDLF := by
  classical
  obtain ⟨V, hV, T, hCount, hAge, hHom, hDLF⟩ :=
    d.exists_countableHomogeneousDLF_of_completeGoodOrbit.{u, v, 0} hOrbit
  letI : ∀ n, Finite (V n) := hV
  refine ⟨T.VertexLimit, T.limitRawPresentation, hCount, ?_, hHom, hDLF⟩
  intro n P
  exact hAge (Fin n) P

/-- The exceptional trivial effective-group branch needs no
good affine congruence orbit or raw reversal-fixed colour. -/
theorem hasCountableHomogeneousDLF_of_subsingleton
    (d : RawDatum G C)
    [Subsingleton G] :
    d.HasCountableHomogeneousDLF := by
  classical
  obtain ⟨V, hV, T, hCount, hAge, hHom, hDLF⟩ :=
    d.exists_countableHomogeneousDLF_of_subsingleton.{u, v, 0}
  letI : ∀ n, Finite (V n) := hV
  refine ⟨T.VertexLimit, T.limitRawPresentation, hCount, ?_, hHom, hDLF⟩
  intro n P
  exact hAge (Fin n) P

/-- The complete DLF iff classification in the exact original
finite binary rectangle language:
  DLF iff (effective group is trivial OR some entire affine
  congruence orbit is realized by raw reversal-fixed colours).

In particular a SINGLE complete good orbit suffices: global
saturation of all good colours is not required. -/
theorem countableHomogeneousDLF_iff
    (d : RawDatum G C) :
    d.HasCountableHomogeneousDLF ↔
      Subsingleton G ∨ d.HasCompleteGoodOrbit := by
  classical
  constructor
  · intro hDLF
    by_cases hSub : Subsingleton G
    · exact Or.inl hSub
    · right
      have hNe : ∃ x y : G, x ≠ y := by
        by_contra hPairs
        apply hSub
        refine ⟨?_⟩
        intro x y
        by_contra hxy
        exact hPairs ⟨x, y, hxy⟩
      letI : Nontrivial G := ⟨hNe⟩
      obtain ⟨X, M, _hCount, hFin, hHom, hDense⟩ := hDLF
      exact M.completeGoodOrbit_of_denseLocallyFinite hFin hHom hDense
  · intro h
    rcases h with hSub | hOrbit
    · letI : Subsingleton G := hSub
      exact d.hasCountableHomogeneousDLF_of_subsingleton
    · exact d.hasCountableHomogeneousDLF_of_completeGoodOrbit hOrbit

end RawDatum
end SemigenericEPPA
