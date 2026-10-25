import SemigenericEPPA.Structure.DLFRawRelativeExtensionFromHomogeneity
import SemigenericEPPA.Structure.DLFOldPartCloneExtension
import SemigenericEPPA.Structure.DLFArbitrarySingletonRawPart
import Mathlib.Data.Finset.Basic

/-!
# Genuine relative finite raw one-point extensions in a homogeneous age limit

These lemmas instantiate the already certified original-language
Fraisse relative embedding theorem for the TWO simplest one-point
raw constructions.

(1) Over ANY prescribed finite vertex set F in a full-age
homogeneous raw rectangle M, realize an arbitrary raw colour
row from a NEW singleton E-class, exactly on the prescribed
vertices of F.

(2) Adjoin a genuinely fresh point in the E-class of any
anchor in F, with exactly the anchor's original raw colours
to the old finite F. The new vertex is provably OUTSIDE F.

Neither construction assumes the finite old part F carries
any pre-existing group action. They are the finite geometric
interfaces needed for the no-involutions half of negative DLF.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Any assigned original raw colours on a finite old vertex
set occur as the row of a genuinely new singleton E-class in
a homogeneous structure with the complete finite raw age. -/
theorem exists_relativeSingletonRawRow_of_fullAge_homogeneous
    (M : RawRectanglePresentation d V)
    (hAge : ∀ (W : Type w) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V,
        Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y))
    (hHom : ∀ (K : Finset V) (p : K → V),
      Function.Injective p →
      (∀ x y : K, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : K, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : K, α.val x.val = p x)
    (F : Finset V)
    (f : {x : V // x ∈ F} → C) :
    ∃ z : V,
      (∀ x : {x : V // x ∈ F}, ¬M.part z x.val) ∧
      (∀ x : {x : V // x ∈ F},
        M.colour z x.val = some (f x)) := by
  classical
  let P : RawRectanglePresentation d {x : V // x ∈ F} :=
    M.pullbackRaw Subtype.val
  let Q : RawRectanglePresentation d (Option {x : V // x ∈ F}) :=
    P.adjoinSingletonPart f
  obtain ⟨t, ht, htPart, htColour⟩ := hAge _ Q
  obtain ⟨j, hj, hjPart, hjColour, hjOld⟩ :=
    P.relative_embedding_of_age_and_homogeneity
      Q M (fun x => some x) Option.some_injective
      (by intro x y; rfl)
      (by intro x y; rfl)
      Subtype.val Subtype.val_injective
      (by intro x y; rfl)
      (by intro x y; rfl)
      t ht htPart htColour hHom
  refine ⟨j none, ?_, ?_⟩
  · intro x h
    have hOld : M.part (j none) (j (some x)) := by
      simpa only [hjOld x] using h
    exact (P.adjoinSingletonPart_newCross f x)
      ((hjPart none (some x)).mp hOld)
  · intro x
    have h := hjColour none (some x)
    have hc : Q.colour none (some x) = some (f x) := rfl
    rw [hc] at h
    simpa only [hjOld x] using h

/-- Over every prescribed finite induced substructure F, clone
one of its vertices in the same E-class without identifying the
new point with ANY of the old vertices. This provides a third
point in any existing E-class over a finite selected pair. -/
theorem exists_freshRelativeOldPartClone_of_fullAge_homogeneous
    (M : RawRectanglePresentation d V)
    (hAge : ∀ (W : Type w) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V,
        Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y))
    (hHom : ∀ (K : Finset V) (p : K → V),
      Function.Injective p →
      (∀ x y : K, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : K, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : K, α.val x.val = p x)
    (F : Finset V)
    (a : {x : V // x ∈ F}) :
    ∃ z : V,
      z ∉ F ∧ M.part z a.val ∧
      (∀ x : {x : V // x ∈ F},
        M.colour z x.val = M.colour a.val x.val) := by
  classical
  let P : RawRectanglePresentation d {x : V // x ∈ F} :=
    M.pullbackRaw Subtype.val
  let Q : RawRectanglePresentation d (Option {x : V // x ∈ F}) :=
    P.adjoinOldPartClone a
  obtain ⟨t, ht, htPart, htColour⟩ := hAge _ Q
  obtain ⟨j, hj, hjPart, hjColour, hjOld⟩ :=
    P.relative_embedding_of_age_and_homogeneity
      Q M (fun x => some x) Option.some_injective
      (by intro x y; rfl)
      (by intro x y; rfl)
      Subtype.val Subtype.val_injective
      (by intro x y; rfl)
      (by intro x y; rfl)
      t ht htPart htColour hHom
  refine ⟨j none, ?_, ?_, ?_⟩
  · intro hz
    let x : {x : V // x ∈ F} := ⟨j none, hz⟩
    have hEq : j none = j (some x) := by
      rw [hjOld x]
    have hFalse : (none : Option {x : V // x ∈ F}) = some x :=
      hj hEq
    cases hFalse
  · have h := (hjPart none (some a)).mpr
      (P.adjoinOldPartClone_samePart a)
    simpa only [hjOld a] using h
  · intro x
    have h := hjColour none (some x)
    have hQ : Q.colour none (some x) = P.colour a x := rfl
    rw [hQ] at h
    simpa only [hjOld x] using h

end RawRectanglePresentation
end SemigenericEPPA
