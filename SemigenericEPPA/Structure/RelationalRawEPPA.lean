import SemigenericEPPA.Structure.RawEPPA
import SemigenericEPPA.Structure.RelationalRoundtrip

/-!
# Ordinary raw EPPA in the literal binary relational language

The explicit finite raw EPPA theorem is first stated for functional
RawRectanglePresentation data. Every genuine relational structure
satisfying R1--R3 admits an exact functional presentation, however:
both the E predicate and each P_c relation survive the round trip.

Consequently, for any finite relational member A of K(G,s,phi),
there is one finite literal raw witness B and one injective map psi
preserving and reflecting every original relation, such that EVERY
injective partial raw automorphism of A extends to an automorphism
of B on its entire old-vertex image.

The result is a genuine relational corollary, not a further
hypothesis about a hypothetical functional presentation.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w

variable {G : Type u} [Group G] {C : Type v} {U : Type w}
variable {d : RawDatum G C}
variable {A : Structure (rectangleLanguage C) U}

/-- The ordinary raw EPPA construction applies to every finite
member of the exact relational class R1--R3, with all E and P_c
predicates preserved and reflected literally. The concrete witness
carrier remains the same finite two-layer valuation carrier. -/
theorem IsRectangleStructure.finite_relationalRawEPPA_witness
    [Finite G] [Finite C] [Finite U]
    (h : IsRectangleStructure d A) :
    Finite (RawEPPAWitnessCarrier h.toRawPresentation) ∧
    ∃ (R : RawRectanglePresentation d
          (RawEPPAWitnessCarrier h.toRawPresentation))
      (ψ : U → RawEPPAWitnessCarrier h.toRawPresentation),
      Function.Injective ψ ∧
      (∀ x y,
        partRel R.toStructure (ψ x) (ψ y) ↔ partRel A x y) ∧
      (∀ c : C, ∀ x y,
        rawRel R.toStructure c (ψ x) (ψ y) ↔ rawRel A c x y) ∧
      (∀ (S : Set U) (p : S → U),
        Function.Injective p →
        (∀ x y : S,
          partRel A x.val y.val ↔ partRel A (p x) (p y)) →
        (∀ x y : S, ∀ c : C,
          rawRel A c x.val y.val ↔ rawRel A c (p x) (p y)) →
        ∃ T : Equiv.Perm
            (RawEPPAWitnessCarrier h.toRawPresentation),
          (∀ x : S, T (ψ x.val) = ψ (p x)) ∧
          (∀ X Y,
            partRel R.toStructure (T X) (T Y) ↔
              partRel R.toStructure X Y) ∧
          (∀ c : C, ∀ X Y,
            rawRel R.toStructure c (T X) (T Y) ↔
              rawRel R.toStructure c X Y)) := by
  let P : RawRectanglePresentation d U := h.toRawPresentation
  obtain ⟨hfin, R, ψ, hψinj, hψpart, hψcolour, hLifts⟩ :=
    P.finite_rawEPPA_witness
  refine ⟨hfin, R, ψ, hψinj, ?_, ?_, ?_⟩
  · intro x y
    exact (hψpart x y).trans Iff.rfl
  · intro c x y
    change R.colour (ψ x) (ψ y) = some c ↔ rawRel A c x y
    rw [hψcolour x y]
    exact h.rawOption_some_iff c x y
  · intro S p hp hE hRaw
    have hPartP : ∀ x y : S,
        P.part x.val y.val ↔ P.part (p x) (p y) := hE
    have hColourP : ∀ x y : S,
        P.colour (p x) (p y) = P.colour x.val y.val := by
      intro x y
      cases hc : P.colour x.val y.val with
      | none =>
          have hpart : partRel A x.val y.val :=
            (h.rawOption_none_iff x.val y.val).mp hc
          have hpart' : partRel A (p x) (p y) :=
            (hE x y).mp hpart
          have hc' : P.colour (p x) (p y) = none :=
            (h.rawOption_none_iff (p x) (p y)).mpr hpart'
          exact hc'.trans hc.symm
      | some c =>
          have hrel : rawRel A c x.val y.val :=
            (h.rawOption_some_iff c x.val y.val).mp hc
          have hrel' : rawRel A c (p x) (p y) :=
            (hRaw x y c).mp hrel
          have hc' : P.colour (p x) (p y) = some c :=
            (h.rawOption_some_iff c (p x) (p y)).mpr hrel'
          exact hc'.trans hc.symm
    obtain ⟨T, hT, hTE, hTRaw⟩ :=
      hLifts S p hp hPartP hColourP
    exact ⟨T, hT, hTE, hTRaw⟩

end SemigenericEPPA
