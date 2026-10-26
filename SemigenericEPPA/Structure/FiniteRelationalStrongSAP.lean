import SemigenericEPPA.Structure.FiniteSAPFromOnePointFinite

/-!
# The exact unconditional finite original-language strong amalgamation property

We record the genuine terminal statement of SAP for K(G,s,φ):
for ANY finite original R1--R3 relational structures A,B,C,
and ANY two induced embeddings f:A↪B, g:A↪C,
there is a finite original R1--R3 structure D and induced
embeddings i:B↪D, j:C↪D such that the common base commutes
and the images intersect exactly in the old base.

We ask additionally that the two images cover ALL vertices of D,
as provided by our one-point strong pushout construction. Thus
no phantom vertices are permitted in the amalgam.

The predicate is a precise final target; the implication
from this property to the local one-point-vs-finite property
is immediate. The converse is under active finite-chain
formalization and is NOT assumed in this module.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

namespace RawDatum

/-- Finite *strong* amalgamation for the full class of literal
E- and ordered R_c-structures satisfying R1--R3, preserving
the ACTUALLY GIVEN induced embeddings and their exact overlap. -/
def HasFiniteRelationalStrongSAP (d : RawDatum G C) : Prop :=
  ∀ {X Y Z : Type (max u v)}
    [Fintype X] [Fintype Y] [Fintype Z]
    {A : Structure (rectangleLanguage C) X}
    {B : Structure (rectangleLanguage C) Y}
    {C₀ : Structure (rectangleLanguage C) Z},
    IsRectangleStructure d A →
    IsRectangleStructure d B →
    IsRectangleStructure d C₀ →
    ∀ (f : Structure.Embedding (rectangleTrivialAction C) A B)
      (g : Structure.Embedding (rectangleTrivialAction C) A C₀),
      ∃ (W : Type (max u v)) (hW : Fintype W)
        (D : Structure (rectangleLanguage C) W),
        IsRectangleStructure d D ∧
        ∃ (i : Structure.Embedding (rectangleTrivialAction C) B D)
          (j : Structure.Embedding (rectangleTrivialAction C) C₀ D),
          StrongSquare
            (fun x : X => f x) (fun x : X => g x)
            (fun y : Y => i y) (fun z : Z => j z)

/-- The final finite SAP statement entails the expected local
relative one-point-vs-finite strong amalgamation interface.
There is NO change of carrier, language, or implicit weakening. -/
theorem hasOnePointAgainstFiniteStrongSAP_of_fullSAP
    (d : RawDatum G C)
    (hSAP : d.HasFiniteRelationalStrongSAP) :
    HasOnePointAgainstFiniteStrongSAP d := by
  intro X Y Z _ _ _ A B D hA hB hD f g _fresh _hout _hcover
  exact hSAP hA hB hD f g

end RawDatum
end SemigenericEPPA
