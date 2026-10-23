import SemigenericEPPA.Structure.RawPresentation

/-!
# Enlarging any old equivalence class by cloning a vertex

The negative DLF argument needs a third vertex in an E-class
containing a nontrivially moved pair a,b. This can be arranged
by a finite induced one-point extension before invoking the
relative safe-group extension property.

Pull back a COMPLETE raw R1--R3 presentation along any map
f : W → V, without assuming f injective. The pulled-back E
includes the kernel of f, and every raw colour is inherited
exactly. All rectangle equations are inherited pointwise.

For an anchor a:V, take W=Option V, f(none)=a and f(some x)=x.
The new none vertex is distinct from EVERY old some x but lies
in the same E-class as a, with the identical raw profile of a
toward all old vertices. The original P embeds as an INDUCED
substructure via some.

No group action is asserted on the clone; semi-coherent EP
must first transfer the original finite group to a larger
witness containing this induced extension. It need not fix the
clone. The subsequent moving-third-point delta lemma handles
this exact situation without a fixed-point assumption.
-/

namespace SemigenericEPPA

universe u v w z
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {W : Type z} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Pullback of a FULL original raw presentation along any map.
The map need not be injective or surjective. -/
def pullbackRaw (P : RawRectanglePresentation d V) (f : W → V) :
    RawRectanglePresentation d W where
  part x y := P.part (f x) (f y)
  part_equiv := by
    constructor
    · intro x
      exact P.part_equiv.refl (f x)
    · intro x y h
      exact P.part_equiv.symm h
    · intro x y z hxy hyz
      exact P.part_equiv.trans hxy hyz
  colour x y := P.colour (f x) (f y)
  colour_none_iff := by
    intro x y
    exact P.colour_none_iff (f x) (f y)
  colour_reverse := by
    intro x y
    exact P.colour_reverse (f x) (f y)
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11
    exact P.rectangle (f x₀) (f x₁) (f y₀) (f y₁)
      hx hy c₀₀ c₀₁ c₁₀ c₁₁ h00 h01 h10 h11

/-- Map the new vertex to anchor a, every old vertex to itself. -/
def cloneOldPartMap (a : V) : Option V → V
  | none => a
  | some x => x

/-- Adjoin a new copy of a in the very same old E-class,
without changing the old structure or any old raw colour. -/
def adjoinOldPartClone
    (P : RawRectanglePresentation d V) (a : V) :
    RawRectanglePresentation d (Option V) :=
  P.pullbackRaw (cloneOldPartMap a)

/-- The induced original E relation is preserved and reflected
on the distinguished old some-section. -/
theorem adjoinOldPartClone_oldPart
    (P : RawRectanglePresentation d V) (a x y : V) :
    (P.adjoinOldPartClone a).part (some x) (some y) ↔
      P.part x y := Iff.rfl

/-- Every old raw E/R_c colour is preserved LITERALLY. -/
theorem adjoinOldPartClone_oldColour
    (P : RawRectanglePresentation d V) (a x y : V) :
    (P.adjoinOldPartClone a).colour (some x) (some y) =
      P.colour x y := rfl

/-- The newly cloned vertex is in the E-class of the anchor. -/
theorem adjoinOldPartClone_samePart
    (P : RawRectanglePresentation d V) (a : V) :
    (P.adjoinOldPartClone a).part none (some a) :=
  P.part_equiv.refl a

/-- All new-to-old raw colours are those of the anchor a. -/
theorem adjoinOldPartClone_profile
    (P : RawRectanglePresentation d V) (a x : V) :
    (P.adjoinOldPartClone a).colour none (some x) =
      P.colour a x := rfl

/-- The old-to-new raw colours are precisely the old-to-anchor
colours, so raw reversal holds without a new choice. -/
theorem adjoinOldPartClone_reverseProfile
    (P : RawRectanglePresentation d V) (a x : V) :
    (P.adjoinOldPartClone a).colour (some x) none =
      P.colour x a := rfl

/-- An old E-pair a,b becomes an E-triple none,some a,some b
of distinct vertices, even if the old class originally had
exactly two vertices. -/
theorem adjoinOldPartClone_thirdPoint
    (P : RawRectanglePresentation d V)
    (a b : V) (hab : P.part a b) (hne : a ≠ b) :
    (P.adjoinOldPartClone a).part none (some a) ∧
    (P.adjoinOldPartClone a).part none (some b) ∧
    ((none : Option V) ≠ some a) ∧
    ((none : Option V) ≠ some b) ∧
    (some a : Option V) ≠ some b := by
  refine ⟨P.adjoinOldPartClone_samePart a, hab, ?_, ?_, ?_⟩
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    exact hne (Option.some.inj h)

end RawRectanglePresentation
end SemigenericEPPA
