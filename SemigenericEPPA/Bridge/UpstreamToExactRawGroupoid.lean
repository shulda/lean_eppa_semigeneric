import SemigenericEPPA.Bridge.ExactRawPartialGroupoid
import SemigenericEPPA.Bridge.RawTypedEPPA

/-!
# Convert literal upstream partial automorphisms into exact raw arrows

The upstream AllThoseEPPA API stores a partial automorphism as a
PartialEquiv of the entire vertex carrier plus a language-group
element. In the original literal rectangle language the group is
the trivial Perm(Fin 0), so the language component is necessarily 1.

The positive coherent construction instead works with exact induced
raw subset arrows S≃T. Given any upstream partial automorphism p of
a literal old RawRectanglePresentation P, take its ACTUAL source and
target subsets and restrict its PartialEquiv to an Equiv between them.
Then prove this restricted equivalence preserves both the original
E relation and EVERY ordered raw P_c.

The conversion never enlarges the partial domain or changes the
original partial map. Establishing equality of conversions for
upstream PartialIsomorphism.Equivalent pairs, and compatibility
with typed upstream CoherentTriple composition, are separate
final API bridge lemmas.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w}
variable {d : RawDatum G C}

/-- Restrict any upstream partial automorphism of P to an ACTUAL
raw-colour preserving bijection between its exact source and
target induced old substructures. -/
noncomputable def RawRectanglePresentation.upstreamToExactRawArrow
    (P : RawRectanglePresentation d A)
    (p : Structure.PartialAutomorphism
      (rectangleTrivialAction C) P.toStructure) :
    RawRectanglePresentation.ExactPartialIso P p.source p.target := by
  classical
  have hlang : p.lang = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  let S : Set A := p.source
  let T : Set A := p.target
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
  let e : S ≃ T := {
    toFun := fun x => ⟨p x.val, p.map_source x.property⟩
    invFun := fun y =>
      ⟨p.toPartialEquiv.symm y.val,
        p.toPartialEquiv.map_target y.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact p.left_inv x.property
    right_inv := by
      intro y
      apply Subtype.ext
      exact p.right_inv y.property
  }
  have hPart (x y : S) :
      P.part (e x).val (e y).val ↔ P.part x.val y.val := by
    have h := hRel none x y
    change P.part (p x.val) (p y.val) ↔
      P.part x.val y.val at h
    exact h
  have hColour (x y : S) :
      P.colour (e x).val (e y).val =
        P.colour x.val y.val := by
    cases hc : P.colour x.val y.val with
    | none =>
        have hp : P.part x.val y.val :=
          (P.colour_none_iff x.val y.val).mp hc
        have hp' : P.part (e x).val (e y).val :=
          (hPart x y).mpr hp
        exact (P.colour_none_iff (e x).val (e y).val).mpr hp'
    | some c =>
        have h := hRel (some c) x y
        change P.colour (p x.val) (p y.val) = some c ↔
          P.colour x.val y.val = some c at h
        exact h.mpr hc
  exact {toEquiv := e, part_iff := hPart, colour_eq := hColour}

end SemigenericEPPA
