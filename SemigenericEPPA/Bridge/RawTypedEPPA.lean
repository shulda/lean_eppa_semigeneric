import SemigenericEPPA.Bridge.RawTypedAutomorphism
import SemigenericEPPA.Structure.RawEPPA
import AllThoseEPPA.EPPA

/-!
# The standard typed IsEPPAWitness interface

The explicit finite raw EPPA construction already yields one raw
R1--R3 witness, an induced old embedding and an extension of every
injective partial map preserving all original raw colours.

This module translates the theorem to the generic definitions of
AllThoseEPPA.Structure.Embedding, PartialAutomorphism, Automorphism,
ExtendsAlong and IsEPPAWitness, using the ACTUAL trivial group of
permutations of the empty type Fin 0 as the language-action group.

In particular, the generic partial automorphism determines a
partial map from its genuine source set. Its injectivity follows
from the underlying PartialEquiv, and its preservation of E and all
raw P_c relations follows from map_rel_iff. The resulting actual
typed automorphism extends it along the typed embedding, including
the language-group equality. This is ordinary, NOT coherent, EPPA.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {d : RawDatum G C}

/-- The truly trivial language-symbol action, expressed using a
canonical group (rather than assuming a missing Group PUnit instance). -/
abbrev rectangleTrivialAction (C : Type v) :=
  Language.Action.trivial (rectangleLanguage C) (Equiv.Perm (Fin 0))

/-- The unconditional raw EPPA witness is also an EPPA witness in
the original shared AllThoseEPPA typed partial-isomorphism API.

The existential witness and its embedding are chosen before p.
The proof returns a genuine typed automorphism, not merely a raw
vertex permutation; its action on the complete source domain and
its language component satisfy ExtendsAlong exactly. -/
theorem RawRectanglePresentation.finite_typedEPPA_witness
    [Finite G] [Finite C] [Finite V]
    (P : RawRectanglePresentation d V) :
    Finite (RawEPPAWitnessCarrier P) ∧
    ∃ (R : RawRectanglePresentation d (RawEPPAWitnessCarrier P))
      (ψ : Structure.Embedding
        (rectangleTrivialAction C) P.toStructure R.toStructure),
      Structure.IsEPPAWitness (rectangleTrivialAction C) ψ := by
  classical
  obtain ⟨hFinite, R, old, hOldInj, hOldPart, hOldColour, hExtend⟩ :=
    P.finite_rawEPPA_witness
  let ψ : Structure.Embedding (rectangleTrivialAction C)
      P.toStructure R.toStructure :=
    P.toTypedEmbedding R old hOldInj hOldPart hOldColour
  refine ⟨hFinite, R, ψ, ?_⟩
  intro p
  have hlang : p.lang = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  let S : Set V := p.source
  let f : S → V := fun x => p x.val
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.val = p.toPartialEquiv.symm (p x.val) :=
        (p.toPartialEquiv.left_inv x.property).symm
      _ = p.toPartialEquiv.symm (p y.val) :=
        congrArg p.toPartialEquiv.symm hxy
      _ = y.val := p.toPartialEquiv.left_inv y.property
  have hRel (name : Option C) (x y : S) :
      P.toStructure.rel (binarySymbol C name)
          (p.toPartialEquiv ∘ pairTuple x.val y.val) ↔
        P.toStructure.rel (binarySymbol C name)
          (pairTuple x.val y.val) := by
    have hdom : ∀ i : Fin 2,
        (pairTuple x.val y.val) i ∈ p.source := by
      intro i
      by_cases hi : i.val = 0
      · simpa [pairTuple, hi] using x.property
      · simpa [pairTuple, hi] using y.property
    have h := p.map_rel_iff
      (binarySymbol C name) (pairTuple x.val y.val) hdom
    rw [hlang, Language.Action.onRel_one] at h
    exact h
  have hPart : ∀ x y : S,
      P.part x.val y.val ↔ P.part (f x) (f y) := by
    intro x y
    have h := hRel none x y
    change P.part (f x) (f y) ↔ P.part x.val y.val at h
    exact h.symm
  have hColour : ∀ x y : S,
      P.colour (f x) (f y) = P.colour x.val y.val := by
    intro x y
    cases hc : P.colour x.val y.val with
    | none =>
        have hsrc : P.part x.val y.val :=
          (P.colour_none_iff x.val y.val).mp hc
        have htgt : P.part (f x) (f y) :=
          (hPart x y).mp hsrc
        exact (P.colour_none_iff (f x) (f y)).mpr htgt
    | some c =>
        have h := hRel (some c) x y
        change P.colour (f x) (f y) = some c ↔
          P.colour x.val y.val = some c at h
        exact h.mpr hc
  obtain ⟨T, hT, hTE, hTraw⟩ :=
    hExtend S f hinj hPart hColour
  have hTColour (x y : RawEPPAWitnessCarrier P) :
      R.colour (T x) (T y) = R.colour x y := by
    cases hc : R.colour x y with
    | none =>
        have hsrc : R.part x y :=
          (R.colour_none_iff x y).mp hc
        have htgt : R.part (T x) (T y) :=
          (hTE x y).mpr hsrc
        exact (R.colour_none_iff (T x) (T y)).mpr htgt
    | some c =>
        have hsrc : rawRel R.toStructure c x y :=
          (R.rawRel_toStructure c x y).mpr hc
        have htgt : rawRel R.toStructure c (T x) (T y) :=
          (hTraw c x y).mpr hsrc
        exact (R.rawRel_toStructure c (T x) (T y)).mp htgt
  let g : Structure.Automorphism (rectangleTrivialAction C)
      R.toStructure :=
    R.toTypedAutomorphism T hTE hTColour
  refine ⟨g, ?_⟩
  constructor
  · change (1 : Equiv.Perm (Fin 0)) * 1 = 1 * p.lang
    rw [hlang]
    simp
  · intro x hx
    change T (old x) = old (p x)
    exact hT ⟨x, hx⟩

end SemigenericEPPA
