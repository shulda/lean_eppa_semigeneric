import SemigenericEPPA.Structure.Pullback
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite induced extensions normalize to an old carrier plus Fin m

Given a finite injective map f : X → Y, decompose the actual
carrier Y into its old image f(X) and the finite complementary
subtype. No additional vertices are introduced, and no old
vertices are identified.

A chosen finite enumeration of the complement turns this
decomposition into an equivalence X ⊕ Fin m ≃ Y, whose
restriction to X is literally f. Pulling back an R1--R3
structure along this equivalence preserves every relation
exactly and yields a genuinely induced original-language
normalization suitable for one-point prefix decomposition.

Nothing here depends on the colours, effective group, EPPA,
or assumptions about a Fraïssé limit.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {C : Type u} {X : Type v} {Y : Type w}

/-- The genuinely new vertices of Y outside the old embedding. -/
abbrev FiniteExtensionComplement (f : X → Y) : Type w :=
  {y : Y // y ∉ Set.range f}

/-- Split any finite carrier into an old injected part and
the exact complement, with no duplicate vertices. -/
noncomputable def extensionSumEquiv
    (f : X → Y) (hf : Function.Injective f) :
    X ⊕ FiniteExtensionComplement f ≃ Y := by
  classical
  let e : X ⊕ FiniteExtensionComplement f → Y
    | Sum.inl x => f x
    | Sum.inr y => y.val
  have he : Function.Injective e := by
    intro a b h
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            exact congrArg Sum.inl (hf h)
        | inr z =>
            exact False.elim (z.property ⟨x, h⟩)
    | inr x =>
        cases b with
        | inl y =>
            exact False.elim (x.property ⟨y, h.symm⟩)
        | inr z =>
            exact congrArg Sum.inr (Subtype.ext h)
  have hs : Function.Surjective e := by
    intro y
    by_cases hy : y ∈ Set.range f
    · obtain ⟨x, hx⟩ := hy
      exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩
  exact Equiv.ofBijective e ⟨he, hs⟩

@[simp] theorem extensionSumEquiv_inl
    (f : X → Y) (hf : Function.Injective f) (x : X) :
    extensionSumEquiv f hf (Sum.inl x) = f x := by
  rfl

/-- Canonical finite-cardinality normalization, with a *chosen*
enumeration of the exact complement. The source is X ⊕ Fin m
and is isomorphic to the original Y. -/
noncomputable def finiteExtensionSumEquiv
    [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Injective f) :
    X ⊕ Fin (Fintype.card (FiniteExtensionComplement f)) ≃ Y := by
  classical
  let complementEquiv :
      Fin (Fintype.card (FiniteExtensionComplement f)) ≃
        FiniteExtensionComplement f :=
    (Fintype.equivFin (FiniteExtensionComplement f)).symm
  exact (Equiv.sumCongr (Equiv.refl X) complementEquiv).trans
    (extensionSumEquiv f hf)

@[simp] theorem finiteExtensionSumEquiv_inl
    [Fintype X] [Fintype Y]
    (f : X → Y) (hf : Function.Injective f) (x : X) :
    finiteExtensionSumEquiv f hf (Sum.inl x) = f x := by
  classical
  simp [finiteExtensionSumEquiv, extensionSumEquiv, Equiv.sumCongr]

/-- Exact normalization of original R1--R3 data on Y, whose
old X subset becomes literally the left summand. -/
noncomputable def normalizedFiniteExtension
    [Fintype X] [Fintype Y]
    (B : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f) :
    Structure (rectangleLanguage C)
      (X ⊕ Fin (Fintype.card (FiniteExtensionComplement f))) :=
  pullbackRectangle B (finiteExtensionSumEquiv f hf)

/-- Every legal original R1--R3 structure remains legal after
canonical finite carrier normalization. -/
theorem IsRectangleStructure.normalizedFiniteExtension
    {G : Type*} [Group G] {d : RawDatum G C}
    [Fintype X] [Fintype Y]
    {B : Structure (rectangleLanguage C) Y}
    (hB : IsRectangleStructure d B)
    (f : X → Y) (hf : Function.Injective f) :
    IsRectangleStructure d (normalizedFiniteExtension B f hf) :=
  hB.pullback (finiteExtensionSumEquiv f hf)

/-- The base X embeds with the *original* name f, as the
left summand of the fully normalized finite extension. -/
theorem normalizedFiniteExtension_oldPart
    [Fintype X] [Fintype Y]
    (B : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f)
    (x y : X) :
    partRel (normalizedFiniteExtension B f hf)
      (Sum.inl x) (Sum.inl y) ↔ partRel B (f x) (f y) := by
  simp [normalizedFiniteExtension]

/-- The ordered original raw colour predicates also survive,
without reducing the palette to effective G-colours. -/
theorem normalizedFiniteExtension_oldRaw
    [Fintype X] [Fintype Y]
    (B : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f)
    (c : C) (x y : X) :
    rawRel (normalizedFiniteExtension B f hf) c
      (Sum.inl x) (Sum.inl y) ↔ rawRel B c (f x) (f y) := by
  simp [normalizedFiniteExtension]

end SemigenericEPPA
