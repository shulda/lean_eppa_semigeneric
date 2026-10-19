import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# The literal raw partial-isomorphism groupoid with exact domains

For the coherent EPPA theorem the relevant objects are induced
vertex subsets of one fixed old raw rectangle structure P, and
arrows are ACTUAL bijections of those subsets preserving the E
relation and EVERY ordered raw colour. Composition is defined only
when the range of the first arrow is exactly the domain of the next.

This module provides the correct dependent type for these arrows,
their identity, inverse, composition, and all groupoid laws. It
does not use partial functions with shrinking domains. The next
C0 assembly can transport stabilizer group homomorphisms and
connector extensions along these exact typed arrows.

No finiteness, homogeneous-limit or coherent-EPPA conclusion is
asserted here.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {A : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- A literal E/raw-colour-preserving isomorphism between two
induced subsets S,T of a fixed raw presentation P. Domains and
targets are exact subtype types, not unspecified partial supports. -/
structure ExactPartialIso
    (P : RawRectanglePresentation d A)
    (S T : Set A) where
  toEquiv : S ≃ T
  part_iff : ∀ x y : S,
    P.part (toEquiv x).val (toEquiv y).val ↔
      P.part x.val y.val
  colour_eq : ∀ x y : S,
    P.colour (toEquiv x).val (toEquiv y).val =
      P.colour x.val y.val

namespace ExactPartialIso

variable {P : RawRectanglePresentation d A}
variable {S T U W : Set A}

/-- Literal map of an exact partial raw isomorphism. -/
instance : CoeFun (ExactPartialIso P S T) (fun _ => S → T) :=
  ⟨fun f => f.toEquiv⟩

/-- An isomorphism is determined by its underlying exact bijection:
the preservation properties are proofs, so proof irrelevance applies. -/
@[ext] theorem ext (f g : ExactPartialIso P S T)
    (heq : f.toEquiv = g.toEquiv) : f = g := by
  cases f
  cases g
  cases heq
  rfl

/-- Identity on an ACTUAL induced subset. -/
def refl (P : RawRectanglePresentation d A) (S : Set A) :
    ExactPartialIso P S S where
  toEquiv := Equiv.refl S
  part_iff := by intro x y; exact Iff.rfl
  colour_eq := by intro x y; rfl

/-- Inverse exact isomorphism with literally reversed domain/range. -/
def symm (f : ExactPartialIso P S T) :
    ExactPartialIso P T S where
  toEquiv := f.toEquiv.symm
  part_iff := by
    intro x y
    have h := f.part_iff (f.toEquiv.symm x) (f.toEquiv.symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm
  colour_eq := by
    intro x y
    have h := f.colour_eq (f.toEquiv.symm x) (f.toEquiv.symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm

/-- Exact groupoid composition g ∘ f, requiring the literal
intermediate set T to match both target and next source. -/
def comp (g : ExactPartialIso P T U)
    (f : ExactPartialIso P S T) :
    ExactPartialIso P S U where
  toEquiv := f.toEquiv.trans g.toEquiv
  part_iff := by
    intro x y
    exact (g.part_iff (f.toEquiv x) (f.toEquiv y)).trans
      (f.part_iff x y)
  colour_eq := by
    intro x y
    exact (g.colour_eq (f.toEquiv x) (f.toEquiv y)).trans
      (f.colour_eq x y)

/-- The exact groupoid identity is a left unit. -/
theorem refl_comp (f : ExactPartialIso P S T) :
    (refl P T).comp f = f := by
  apply ext
  apply Equiv.ext
  intro x
  rfl

/-- The exact groupoid identity is a right unit. -/
theorem comp_refl (f : ExactPartialIso P S T) :
    f.comp (refl P S) = f := by
  apply ext
  apply Equiv.ext
  intro x
  rfl

/-- Composition on exact induced subsets is strictly associative. -/
theorem comp_assoc
    (f : ExactPartialIso P S T)
    (g : ExactPartialIso P T U)
    (h : ExactPartialIso P U W) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  apply Equiv.ext
  intro x
  rfl

/-- A partial isomorphism followed by its inverse is exactly the
identity arrow on its source. -/
theorem symm_comp (f : ExactPartialIso P S T) :
    f.symm.comp f = refl P S := by
  apply ext
  apply Equiv.ext
  intro x
  exact f.toEquiv.symm_apply_apply x

/-- The reverse composition is the exact target identity. -/
theorem comp_symm (f : ExactPartialIso P S T) :
    f.comp f.symm = refl P T := by
  apply ext
  apply Equiv.ext
  intro x
  exact f.toEquiv.apply_symm_apply x

end ExactPartialIso

end RawRectanglePresentation

end SemigenericEPPA
