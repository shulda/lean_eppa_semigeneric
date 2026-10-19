import SemigenericEPPA.Bridge.ExactRawPartialGroupoid
import Mathlib.Data.Quot

/-!
# Connected components of the exact old raw-isomorphism groupoid

For a fixed raw rectangle presentation P, two induced old subsets
S,T⊆A lie in the same component precisely when there is a literal
E- and raw-colour-preserving bijection S≃T.

This is an equivalence relation by the ALREADY certified exact
groupoid identity, inverse and composition. Quotienting the full
set of induced old subsets by this relation produces a concrete
component type, even for the empty old subset or empty original
A.

Choose a canonical representative q.out for each quotient
component q, and an exact raw connector from this representative
to EVERY induced old subset in that class. This connector is chosen
ONCE based on P and the component, not per partial map.

The remaining C0 gate selects whole-witness extensions of those
connectors using ordinary raw EPPA and group lifts of the
automorphism group of each representative, then applies the
strictly coherent conjugation formula.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v} {A : Type w}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The literal raw-isomorphism relation on all induced subsets. -/
def rawIsoSetoid (P : RawRectanglePresentation d A) :
    Setoid (Set A) where
  r S T := Nonempty (ExactPartialIso P S T)
  iseqv := by
    constructor
    · intro S
      exact ⟨ExactPartialIso.refl P S⟩
    · intro S T h
      obtain ⟨f⟩ := h
      exact ⟨f.symm⟩
    · intro S T U h₁ h₂
      obtain ⟨f⟩ := h₁
      obtain ⟨g⟩ := h₂
      exact ⟨g.comp f⟩

/-- Canonical type of connected components / old induced
isomorphism types of the exact raw partial-isomorphism groupoid. -/
abbrev RawIsoComponent (P : RawRectanglePresentation d A) :=
  Quotient (P.rawIsoSetoid)

/-- The preselected representative subset for an isomorphism
component. The arbitrary choice is fixed at the quotient level. -/
noncomputable def rawIsoRepresentative
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P) : Set A :=
  q.out

/-- The representative has the selected quotient class literally. -/
theorem rawIsoRepresentative_class
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P) :
    Quotient.mk P.rawIsoSetoid (P.rawIsoRepresentative q) = q := by
  exact Quotient.out_eq q

/-- A particular object/subset together with proof of its exact
component label; this avoids dependent casts between different
representative types in one-component groupoid composition. -/
abbrev RawComponentObject
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P) :=
  {S : Set A // Quotient.mk P.rawIsoSetoid S = q}

/-- The full family of raw groupoid objects in the q component,
as literal induced old subsets. -/
def rawComponentObjects
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P) :
    RawComponentObject P q → Set A :=
  Subtype.val

/-- Every induced old subset in component q admits a literal
E/colour-preserving old connector FROM the FIXED q representative.
No choice of a whole-witness automorphism is made here. -/
noncomputable def rawComponentConnector
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P)
    (i : RawComponentObject P q) :
    ExactPartialIso P (P.rawIsoRepresentative q) i.val := by
  classical
  have heq :
      Quotient.mk P.rawIsoSetoid (P.rawIsoRepresentative q) =
        Quotient.mk P.rawIsoSetoid i.val :=
    (P.rawIsoRepresentative_class q).trans i.property.symm
  exact Classical.choice (Quotient.exact heq)

end RawRectanglePresentation

end SemigenericEPPA
