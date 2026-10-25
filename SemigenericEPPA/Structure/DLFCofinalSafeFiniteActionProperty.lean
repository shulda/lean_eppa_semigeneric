import SemigenericEPPA.Structure.DLFSafePairOverAgeExtension
import SemigenericEPPA.Structure.DLFGOneSafePairOverAgeExtension
import SemigenericEPPA.Structure.DLFTrivialSafePairSeed

/-!
# The cofinal safe-pair finite group extension property

This is the genuine finite H-action property underlying the
positive semi-coherent/DLF construction, phrased solely in the
original E/Option-C raw language.

The selected cofinal family consists of ALL finite safe pairs
(A,H), with H a genuine finite subgroup of Aut_raw(A),
not a subgroup of an auxiliary effective colour group.

(1) Every finite original raw age member P has the safe seed
(P,{1}), hence the family's underlying structures are cofinal.
(2) For any safe (A,H) and any arbitrary finite age extension
A -> P (P need not carry any H action), there is one finite safe
(B,K), an exact induced P -> B embedding, and a faithful
equivariant group embedding H -> K. EVERY original partial raw
automorphism of P extends to an element of this SAME K.

Both positive DLF hypotheses imply this finite property:
a complete good affine orbit, or G=1 with no good-colour
assumption. This does NOT formalize the general converse between
Sagi's semi-coherent property and DLF, nor claim that every
arbitrary cofinal family consists of locally safe pairs.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]

namespace RawDatum

/-- Exact cofinal safe finite-action extension property in a fixed
carrier universe. The relative extension clause does NOT assume
an H-action on the extra vertices of P. -/
def HasCofinalSafeFiniteGroupExtension
    (d : RawDatum G C) : Prop :=
  (∀ (X : Type (max u v)) [Finite X]
      (P : RawRectanglePresentation d X),
      ∃ A : FiniteSafeRawPair d X, A.raw = P) ∧
  (∀ (V X : Type (max u v)) [Finite V] [Finite X]
      (A : FiniteSafeRawPair d V)
      (P : RawRectanglePresentation d X)
      (e0 : V → X)
      (he0inj : Function.Injective e0)
      (he0part : ∀ x y : V,
        P.part (e0 x) (e0 y) ↔ A.raw.part x y)
      (he0colour : ∀ x y : V,
        P.colour (e0 x) (e0 y) = A.raw.colour x y),
      ∃ (W : Type (max u v)) (hW : Finite W),
        letI : Finite W := hW
        ∃ (B : FiniteSafeRawPair d W)
          (f : FiniteSafeRawPairEmbedding A B)
          (eP : X → W),
          Function.Injective eP ∧
          (∀ x y : X,
            B.raw.part (eP x) (eP y) ↔ P.part x y) ∧
          (∀ x y : X,
            B.raw.colour (eP x) (eP y) = P.colour x y) ∧
          (∀ x : V, f.vertex x = eP (e0 x)) ∧
          (∀ (T : Set X) (p : T → X),
            Function.Injective p →
            (∀ x y : T, P.part x.val y.val ↔
              P.part (p x) (p y)) →
            (∀ x y : T, P.colour (p x) (p y) =
              P.colour x.val y.val) →
            ∃ k : B.subgroup,
              ∀ x : T, k.val.val (eP x.val) = eP (p x)))

/-- The selected family of all finite safe raw pairs is cofinal,
and has arbitrary relative semi-coherent finite group extensions,
provided just ONE complete good affine congruence orbit exists. -/
theorem hasCofinalSafeFiniteGroupExtension_of_completeGoodOrbit
    (d : RawDatum G C)
    (hOrbit : d.HasCompleteGoodOrbit) :
    d.HasCofinalSafeFiniteGroupExtension := by
  classical
  constructor
  · intro X _ P
    exact ⟨P.trivialSafePair, rfl⟩
  · intro V X _ _ A P e0 he0inj he0part he0colour
    letI : Fintype V := Fintype.ofFinite V
    letI : Fintype X := Fintype.ofFinite X
    exact A.exists_safeExtension_overRawEmbedding
      P e0 he0inj he0part he0colour hOrbit

/-- Exceptional G=1: the same cofinal safe finite-action extension
family exists EVEN IF there is no globally reversal-fixed raw
colour and hence no complete good orbit. -/
theorem hasCofinalSafeFiniteGroupExtension_of_subsingleton
    (d : RawDatum G C)
    [Subsingleton G] :
    d.HasCofinalSafeFiniteGroupExtension := by
  classical
  constructor
  · intro X _ P
    exact ⟨P.trivialSafePair, rfl⟩
  · intro V X _ _ A P e0 he0inj he0part he0colour
    letI : Fintype V := Fintype.ofFinite V
    letI : Fintype X := Fintype.ofFinite X
    exact A.exists_gOneSafeExtension_overRawEmbedding
      P e0 he0inj he0part he0colour

/-- The exact DLF algebraic criterion implies a concrete cofinal
finite safe-pair semi-coherent extension family. No Sagi bridge is
invoked in the proof. -/
theorem hasCofinalSafeFiniteGroupExtension_of_dlfCriterion
    (d : RawDatum G C)
    (h : Subsingleton G ∨ d.HasCompleteGoodOrbit) :
    d.HasCofinalSafeFiniteGroupExtension := by
  rcases h with hSub | hOrbit
  · letI : Subsingleton G := hSub
    exact d.hasCofinalSafeFiniteGroupExtension_of_subsingleton
  · exact d.hasCofinalSafeFiniteGroupExtension_of_completeGoodOrbit
      hOrbit

end RawDatum
end SemigenericEPPA
