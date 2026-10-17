import SemigenericEPPA.Structure.Induced
import Mathlib.Data.Setoid.Basic

/-!
# The canonical imaginary sort of E-parts

The manuscript's quotient A/E is functorial for maps that preserve
E-equivalence. Exact reflection gives injection on part imaginaries,
so in particular an induced substructure has its expected induced
subset of A/E.

This is independent of chosen transversals/gauges and uses no EPPA
existence results.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t

variable {C : Type u} {G : Type w} [Group G]
variable {d : RawDatum G C}

/-- The canonical imaginary sort, i.e. the quotient of real vertices
by the actual E equivalence relation. -/
abbrev PartQuotient {V : Type v}
    {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) : Type v :=
  Quotient h.partSetoid

/-- Send a real vertex to its canonical E-class imaginary. -/
def partClass {V : Type v} {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) (x : V) : PartQuotient h :=
  Quotient.mk h.partSetoid x

/-- Two vertices determine the same imaginary iff they are E-related. -/
theorem partClass_eq_iff {V : Type v} {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) (x y : V) :
    partClass h x = partClass h y ↔ partRel A x y := by
  constructor
  · intro heq
    exact Quotient.exact heq
  · intro hxy
    exact Quotient.sound hxy

/-- The map on imaginary parts induced by a real map preserving E.
No injectivity or finiteness assumptions are needed for well-definedness. -/
def partQuotientMap
    {V : Type v} {W : Type z}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (hA : IsRectangleStructure d A) (hB : IsRectangleStructure d B)
    (f : V → W)
    (hpres : ∀ x y, partRel A x y → partRel B (f x) (f y)) :
    PartQuotient hA → PartQuotient hB :=
  Quotient.lift (fun x => partClass hB (f x)) (by
    intro x y hxy
    exact Quotient.sound (hpres x y hxy))

@[simp] theorem partQuotientMap_class
    {V : Type v} {W : Type z}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (hA : IsRectangleStructure d A) (hB : IsRectangleStructure d B)
    (f : V → W)
    (hpres : ∀ x y, partRel A x y → partRel B (f x) (f y))
    (x : V) :
    partQuotientMap hA hB f hpres (partClass hA x) =
      partClass hB (f x) := rfl

/-- Reflection of E makes the induced imaginary map injective. -/
theorem partQuotientMap_injective
    {V : Type v} {W : Type z}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (hA : IsRectangleStructure d A) (hB : IsRectangleStructure d B)
    (f : V → W)
    (hpres : ∀ x y, partRel A x y → partRel B (f x) (f y))
    (hreflect : ∀ x y, partRel B (f x) (f y) → partRel A x y) :
    Function.Injective (partQuotientMap hA hB f hpres) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      exact hreflect x y (Quotient.exact hab)

/-- Functoriality of the imaginary sort, at the level of actual
pointwise equality (not merely equality up to some gauge). -/
theorem partQuotientMap_comp
    {V : Type v} {W : Type z} {X : Type t}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    {D : Structure (rectangleLanguage C) X}
    (hA : IsRectangleStructure d A)
    (hB : IsRectangleStructure d B)
    (hD : IsRectangleStructure d D)
    (f : V → W) (g : W → X)
    (hf : ∀ x y, partRel A x y → partRel B (f x) (f y))
    (hg : ∀ x y, partRel B x y → partRel D (g x) (g y))
    (q : PartQuotient hA) :
    partQuotientMap hA hD (g ∘ f)
      (fun x y hxy => hg (f x) (f y) (hf x y hxy)) q =
    partQuotientMap hB hD g hg (partQuotientMap hA hB f hf q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    rfl

/-- Canonical map from E-classes of an induced substructure into
the original E-class quotient. -/
def inducedPartQuotientMap
    {V : Type v} {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) (S : Set V) :
    PartQuotient (h.induced S) → PartQuotient h :=
  partQuotientMap (h.induced S) h Subtype.val
    (fun x y hxy => (inducedRectangle_part A S x y).1 hxy)

/-- Adding the canonical part-imaginary sort does not identify two
different parts of an induced substructure. -/
theorem inducedPartQuotientMap_injective
    {V : Type v} {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A) (S : Set V) :
    Function.Injective (inducedPartQuotientMap h S) := by
  exact partQuotientMap_injective (h.induced S) h Subtype.val
    (fun x y hxy => (inducedRectangle_part A S x y).1 hxy)
    (fun x y hxy => (inducedRectangle_part A S x y).2 hxy)

end SemigenericEPPA
