import SemigenericEPPA.Valuations.PaddedPartialPermutations

/-!
# Exact old partial isomorphisms survive effective uniform padding

The E0 padding changes the old vertex type V to (V/E) × V.  The old
partial domain must therefore be transported to a literal subtype
of that new carrier, rather than silently reusing its old type.

We define precisely that subtype and its partial map.  If the old
partial map preserves/reflection E and preserves every cross-part
effective group colour, its padded copy is an equally exact partial
isomorphism of the verified uniform padded effective geometry.
The proofs use the previously checked injectivity, E-reflection,
and *literal* effective F-preservation of the old embedding.

This supplies the correct typed input to the actual partial gauge
multiplier theorem and eventually the witness construction.  No
hypothetical extension or HKN black box is used.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

variable (D : EffectiveGeometry s V)

/-- Exactly the image of an old partial domain under x ↦ ([x],x),
expressed as a decidable-free predicate on the padded carrier. -/
def paddedPartialDomain (S : Set V) : Set (Quotient D.part × V) :=
  { z | z.1 = Quotient.mk D.part z.2 ∧ z.2 ∈ S }

/-- The old vertex x, considered as an element of the canonical
padded old-domain subtype. -/
def paddedPartialOld (S : Set V) (x : S) :
    D.paddedPartialDomain S :=
  ⟨D.paddedOldMap x.val, ⟨rfl, x.property⟩⟩

/-- The concrete partial map on the padded old image. -/
def paddedPartialMap (S : Set V) (p : S → V)
    (z : D.paddedPartialDomain S) : Quotient D.part × V :=
  D.paddedOldMap (p ⟨z.val.2, z.property.2⟩)

@[simp] theorem paddedPartialMap_old
    (S : Set V) (p : S → V) (x : S) :
    D.paddedPartialMap S p (D.paddedPartialOld S x) =
      D.paddedOldMap (p x) := rfl

/-- Every point of the padded partial domain is literally an old
embedded vertex. -/
theorem paddedPartialDomain_eq_old (S : Set V)
    (z : D.paddedPartialDomain S) :
    z.val = D.paddedOldMap z.val.2 := by
  apply Prod.ext
  · exact z.property.1
  · rfl

/-- The padded partial map is injective whenever the old map is. -/
theorem paddedPartialMap_injective
    (S : Set V) (p : S → V) (hp : Function.Injective p) :
    Function.Injective (D.paddedPartialMap S p) := by
  intro x y hxy
  apply Subtype.ext
  have hreal :
      p ⟨x.val.2, x.property.2⟩ =
        p ⟨y.val.2, y.property.2⟩ :=
    D.paddedOldMap_injective hxy
  have hsecond : x.val.2 = y.val.2 :=
    congrArg Subtype.val (hp hreal)
  apply Prod.ext
  · calc
      x.val.1 = Quotient.mk D.part x.val.2 := x.property.1
      _ = Quotient.mk D.part y.val.2 :=
        congrArg (Quotient.mk D.part) hsecond
      _ = y.val.1 := y.property.1.symm
  · exact hsecond

/-- Exact E-preservation and reflection for the transferred
old partial domain, with no equal-size hypothesis on original
classes and no dependence on arbitrary same-part F-values. -/
theorem paddedPartialMap_part_iff
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y))
    (x y : D.paddedPartialDomain S) :
    D.uniformPaddedGeometry.part x.val y.val ↔
      D.uniformPaddedGeometry.part
        (D.paddedPartialMap S p x)
        (D.paddedPartialMap S p y) := by
  let a : S := ⟨x.val.2, x.property.2⟩
  let b : S := ⟨y.val.2, y.property.2⟩
  calc
    D.uniformPaddedGeometry.part x.val y.val ↔
        D.part x.val.2 y.val.2 := by
          rw [D.paddedPartialDomain_eq_old S x,
            D.paddedPartialDomain_eq_old S y]
          exact D.paddedOldMap_part _ _
    _ ↔ D.part (p a) (p b) := hE a b
    _ ↔ D.uniformPaddedGeometry.part
        (D.paddedPartialMap S p x)
        (D.paddedPartialMap S p y) :=
          (D.paddedOldMap_part (p a) (p b)).symm

/-- Exact preservation of actual group-valued effective cross-colours
on the padded partial domain; not merely gauge-equivalence. -/
theorem paddedPartialMap_crossColour
    (S : Set V) (p : S → V)
    (hE : ∀ x y : S, D.part x.val y.val ↔ D.part (p x) (p y))
    (hF : ∀ x y : S, ¬D.part x.val y.val →
      D.F (p x) (p y) = D.F x.val y.val)
    (x y : D.paddedPartialDomain S)
    (hxy : ¬D.uniformPaddedGeometry.part x.val y.val) :
    D.uniformPaddedGeometry.F
        (D.paddedPartialMap S p x)
        (D.paddedPartialMap S p y) =
      D.uniformPaddedGeometry.F x.val y.val := by
  let a : S := ⟨x.val.2, x.property.2⟩
  let b : S := ⟨y.val.2, y.property.2⟩
  have hcross : ¬D.part x.val.2 y.val.2 := by
    intro h
    apply hxy
    rw [D.paddedPartialDomain_eq_old S x,
      D.paddedPartialDomain_eq_old S y]
    exact (D.paddedOldMap_part _ _).mpr h
  have htarget : ¬D.part (p a) (p b) := by
    intro h
    exact hcross ((hE a b).mpr h)
  calc
    D.uniformPaddedGeometry.F
        (D.paddedPartialMap S p x)
        (D.paddedPartialMap S p y) =
      D.F (p a) (p b) :=
        D.paddedOldMap_crossColour (p a) (p b) htarget
    _ = D.F x.val.2 y.val.2 := hF a b hcross
    _ = D.uniformPaddedGeometry.F x.val y.val := by
      rw [D.paddedPartialDomain_eq_old S x,
        D.paddedPartialDomain_eq_old S y]
      exact (D.paddedOldMap_crossColour _ _ hcross).symm

end EffectiveGeometry

end SemigenericEPPA
