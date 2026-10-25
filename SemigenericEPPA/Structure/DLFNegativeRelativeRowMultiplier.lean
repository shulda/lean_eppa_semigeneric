import SemigenericEPPA.Structure.DLFRawRelativeExtensionFromHomogeneity
import SemigenericEPPA.Structure.DLFOldPartCloneExtension
import SemigenericEPPA.Structure.DLFArbitrarySingletonRawPart
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import Mathlib.Data.Finset.Basic

/-!
# Relative realization of arbitrary left-multiplied raw rows across one pair

The negative DLF cross-involution obstruction needs the following
explicit Fraisse extension fact: for x and y in different E-classes,
and any a in the effective group, one can find a new z E x with
F(z,y)=a*F(x,y).

It is enough to construct the THREE-VERTEX finite raw presentation
with two vertices in one E-class and a singleton opposite class.
The arbitrary prescribed raw colour of z->y is compatible with the
rectangle axiom because the opposite class is a singleton.

Using the already certified literal relative-age-from-homogeneity
lemma, an induced copy of this three-vertex presentation can be
placed over the PARTICULAR existing pair (x,y) in a universal
homogeneous raw rectangle. No global row-assignment, gauge
normalization or unjustified automorphism action is assumed.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

/-- All vertices belong to one E-class, with no cross raw colours. -/
def fullOnePartBoolRaw (d : RawDatum G C) :
    RawRectanglePresentation d Bool where
  part := fun _ _ => True
  part_equiv := ⟨fun _ => trivial,
    fun _ _ _ => trivial,
    fun _ _ _ _ _ => trivial⟩
  colour := fun _ _ => none
  colour_none_iff := by
    intro x y
    constructor <;> intro _ <;> trivial
  colour_reverse := by intro x y; rfl
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁ h₀₀ h₀₁ h₁₀ h₁₁
    cases h₀₀

/-- false represents old x and true represents old y. -/
def crossPairActual (x y : V) (b : Bool) : V :=
  if b then y else x

/-- Old x is some false; old y is none; some true is the fresh clone. -/
def crossPairIntoTriple (b : Bool) : Option Bool :=
  if b then none else some false

namespace RawRectanglePresentation

/-- Finite three-vertex induced extension allowing ANY effective
left multiplier at the additional vertex in the E-class of x. -/
theorem exists_threeVertex_leftMultiplier
    (P : RawRectanglePresentation d V)
    (x y : V) (hxy : ¬P.part x y)
    (a : G) :
    ∃ Q : RawRectanglePresentation d (Option Bool),
      (∀ b c : Bool,
        Q.part (crossPairIntoTriple b) (crossPairIntoTriple c) ↔
          (P.pullbackRaw (crossPairActual x y)).part b c) ∧
      (∀ b c : Bool,
        Q.colour (crossPairIntoTriple b) (crossPairIntoTriple c) =
          (P.pullbackRaw (crossPairActual x y)).colour b c) ∧
      Q.part (some false) (some true) ∧
      ∃ c : C, Q.colour (some true) none = some c ∧
        d.phi c = a * P.effectiveReduct.F x y := by
  classical
  have hcolour : ∃ c : C, P.colour x y = some c := by
    cases h : P.colour x y with
    | none => exact False.elim (hxy ((P.colour_none_iff x y).1 h))
    | some c => exact ⟨c, h⟩
  obtain ⟨c₀, hc₀⟩ := hcolour
  obtain ⟨c₁, hc₁⟩ :=
    d.phi_surjective (a * P.effectiveReduct.F x y)
  let f : Bool → C := fun b =>
    if b then d.reverse c₁ else d.reverse c₀
  let Q : RawRectanglePresentation d (Option Bool) :=
    (fullOnePartBoolRaw d).adjoinSingletonPart f
  have hxx : P.part x x := P.part_equiv.refl x
  have hyy : P.part y y := P.part_equiv.refl y
  have hyx : ¬P.part y x := by
    intro h
    exact hxy (P.part_equiv.symm h)
  have hxxCol : P.colour x x = none :=
    (P.colour_none_iff x x).2 hxx
  have hyyCol : P.colour y y = none :=
    (P.colour_none_iff y y).2 hyy
  have hyxCol : P.colour y x = some (d.reverse c₀) := by
    rw [P.colour_reverse x y, hc₀]
    rfl
  refine ⟨Q, ?_, ?_, ?_, c₁, ?_, hc₁⟩
  · intro b c
    cases b <;> cases c <;>
      simp [Q, crossPairIntoTriple, crossPairActual,
        RawRectanglePresentation.adjoinSingletonPart,
        RawRectanglePresentation.pullbackRaw,
        singletonNewPartRel, fullOnePartBoolRaw,
        hxx, hyy, hxy, hyx]
  · intro b c
    cases b <;> cases c <;>
      simp [Q, f, crossPairIntoTriple, crossPairActual,
        RawRectanglePresentation.adjoinSingletonPart,
        RawRectanglePresentation.pullbackRaw,
        singletonNewPartColour, fullOnePartBoolRaw,
        hc₀, hyxCol, hxxCol, hyyCol, d.reverse_involutive]
  · trivial
  · simp [Q, f, RawRectanglePresentation.adjoinSingletonPart,
      singletonNewPartColour, d.reverse_involutive]

/-- Full finite original-language age together with finite-partial
ultrahomogeneity realizes EVERY effective left multiplier in the
class of x, with y fixed as an already prescribed old vertex. -/
theorem leftMultiplierRows_of_fullAge_homogeneous
    (M : RawRectanglePresentation d V)
    (hAge : ∀ (W : Type) [Fintype W]
      (Q : RawRectanglePresentation d W),
      ∃ t : W → V,
        Function.Injective t ∧
        (∀ x y : W, M.part (t x) (t y) ↔ Q.part x y) ∧
        (∀ x y : W, M.colour (t x) (t y) = Q.colour x y))
    (hHom : ∀ (F : Finset V) (p : F → V),
      Function.Injective p →
      (∀ x y : F, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : F, M.colour (p x) (p y) = M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : F, α.val x.val = p x)
    (x y : V) (hxy : ¬M.part x y) :
    ∀ a : G, ∃ z : V,
      M.part x z ∧
      M.effectiveReduct.F z y =
        a * M.effectiveReduct.F x y := by
  classical
  intro a
  obtain ⟨Q, hQpart, hQcolour, hQxz, c₁, hQc₁, hc₁⟩ :=
    M.exists_threeVertex_leftMultiplier x y hxy a
  let P : RawRectanglePresentation d Bool :=
    M.pullbackRaw (crossPairActual x y)
  let e : Bool → Option Bool := crossPairIntoTriple
  have he : Function.Injective e := by
    intro b c h
    cases b <;> cases c <;>
      simp [e, crossPairIntoTriple] at h ⊢
  let old : Bool → V := crossPairActual x y
  have hneq : x ≠ y := by
    intro h
    apply hxy
    simpa only [h] using M.part_equiv.refl y
  have hold : Function.Injective old := by
    intro b c h
    cases b <;> cases c <;>
      simp [old, crossPairActual, hneq] at h ⊢
  obtain ⟨t, ht, htPart, htColour⟩ := hAge (Option Bool) Q
  obtain ⟨j, hj, hjPart, hjColour, hjOld⟩ :=
    P.relative_embedding_of_age_and_homogeneity
      Q M e he hQpart hQcolour
      old hold
      (by intro b c; rfl)
      (by intro b c; rfl)
      t ht htPart htColour hHom
  have hjx : j (some false) = x := by
    simpa only [e, crossPairIntoTriple, old, crossPairActual]
      using hjOld false
  have hjy : j none = y := by
    simpa only [e, crossPairIntoTriple, old, crossPairActual]
      using hjOld true
  let z : V := j (some true)
  have hxz : M.part x z := by
    have h := (hjPart (some false) (some true)).2 hQxz
    simpa only [z, hjx] using h
  have hcol : M.colour z y = some c₁ := by
    have h := (hjColour (some true) none).trans hQc₁
    simpa only [z, hjy] using h
  refine ⟨z, hxz, ?_⟩
  calc
    M.effectiveReduct.F z y = d.phi c₁ :=
      (M.effectiveReduct_crossColour z y c₁ hcol).symm
    _ = a * M.effectiveReduct.F x y := hc₁

end RawRectanglePresentation
end SemigenericEPPA
