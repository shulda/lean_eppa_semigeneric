import SemigenericEPPA.Structure.Pullback
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Set

/-!
# Canonical finite normal form of an arbitrary induced extension

For any injective map f : X → Y with finite Y, there is a genuine
bijection X ⊕ Fin m ≃ Y whose restriction to the X-summand is exactly f.
The extra indices enumerate the complement of the *actual* image of f.

Pulling back an arbitrary original E/R_c rectangle along this
bijection preserves all R1--R3 axioms and ALL ordered colours, not
merely the effective G-valued reduct. Thus an arbitrary finite
embedded extension can be put into the precise canonical shape
needed for the finite-prefix one-point-chain and full SAP proofs.

No linear ordering on Y, its E-parts, or raw colours is assumed;
the complement enumeration is a noncomputable finite choice.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

/-- The exact number of vertices outside the image of f. -/
noncomputable def finiteExtensionExtraCount
    {X : Type u} {Y : Type v} [Finite Y] (f : X → Y) : ℕ :=
  Nat.card { y : Y // y ∉ Set.range f }

/-- Every injective map into a finite carrier is canonically
normalizable to a left-summand inclusion plus finitely many new
vertices. The resulting equivalence agrees with f ON THE NOSE. -/
noncomputable def finiteExtensionNormalEquiv
    {X : Type u} {Y : Type v} [Finite Y]
    (f : X → Y) (hf : Function.Injective f) :
    X ⊕ Fin (finiteExtensionExtraCount f) ≃ Y := by
  classical
  let S := { y : Y // y ∉ Set.range f }
  letI : Fintype S := Fintype.ofFinite S
  let eOld : X ≃ { y : Y // y ∈ Set.range f } :=
    Equiv.ofInjective f hf
  let eNew : Fin (finiteExtensionExtraCount f) ≃ S := by
    simpa only [finiteExtensionExtraCount, Nat.card_eq_fintype_card]
      using (Fintype.equivFin S).symm
  exact (eOld.sumCongr eNew).trans
    (Equiv.sumCompl (fun y : Y => y ∈ Set.range f))

@[simp] theorem finiteExtensionNormalEquiv_old
    {X : Type u} {Y : Type v} [Finite Y]
    (f : X → Y) (hf : Function.Injective f) (x : X) :
    finiteExtensionNormalEquiv f hf (Sum.inl x) = f x := by
  classical
  simp [finiteExtensionNormalEquiv]

variable {G : Type z} [Group G] {C : Type w}

/-- The induced original-language structure on the canonical
normal form of a finite embedded extension. -/
noncomputable def finiteExtensionNormalStructure
    {X : Type u} {Y : Type v} [Finite Y]
    (P : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f) :
    Structure (rectangleLanguage C)
      (X ⊕ Fin (finiteExtensionExtraCount f)) :=
  pullbackRectangle P (finiteExtensionNormalEquiv f hf)

/-- Normalization preserves the exact original R1--R3 class,
with no assumption on the effective group or the parameter s. -/
theorem IsRectangleStructure.finiteExtensionNormal
    {X : Type u} {Y : Type v} [Finite Y]
    {d : RawDatum G C}
    {P : Structure (rectangleLanguage C) Y}
    (hP : IsRectangleStructure d P)
    (f : X → Y) (hf : Function.Injective f) :
    IsRectangleStructure d
      (finiteExtensionNormalStructure P f hf) :=
  hP.pullback (finiteExtensionNormalEquiv f hf)

/-- On the distinguished old vertices, the canonical
normalization preserves and reflects E *exactly*. -/
theorem finiteExtensionNormal_part_old
    {X : Type u} {Y : Type v} [Finite Y]
    (P : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f) (x y : X) :
    partRel (finiteExtensionNormalStructure P f hf)
      (Sum.inl x) (Sum.inl y) ↔
      partRel P (f x) (f y) := by
  simp [finiteExtensionNormalStructure]

/-- Likewise for every ordered original raw relation R_c. -/
theorem finiteExtensionNormal_raw_old
    {X : Type u} {Y : Type v} [Finite Y]
    (P : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f)
    (c : C) (x y : X) :
    rawRel (finiteExtensionNormalStructure P f hf)
      c (Sum.inl x) (Sum.inl y) ↔
      rawRel P c (f x) (f y) := by
  simp [finiteExtensionNormalStructure]

/-- This is a genuine identity-language structure embedding
whose carrier map is the normalization equivalence. -/
noncomputable def finiteExtensionNormal_embedding
    {X : Type u} {Y : Type v} [Finite Y]
    {Γ : Type*} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (P : Structure (rectangleLanguage C) Y)
    (f : X → Y) (hf : Function.Injective f) :
    Structure.Embedding act
      (finiteExtensionNormalStructure P f hf) P :=
  pullbackRectangle_embedding act P
    (finiteExtensionNormalEquiv f hf)
    (finiteExtensionNormalEquiv f hf).injective

end SemigenericEPPA
