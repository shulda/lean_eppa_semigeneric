import SemigenericEPPA.Structure.DLFOldPartCloneExtension
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# Literal effective-reduct agreement for any induced raw pullback

The positive DLF proof moves between the literal raw R1--R3
language and its canonical effective G-valued reduct. The
effective reduct is defined through a choice of raw labels on
cross-E pairs, so equality on embedded substructures should
be proved, not treated as a definitional equality.

For ANY map f:W→V, the raw pullback P.pullbackRaw f has exactly
the original E and raw-colour functions evaluated on f(x),f(y).
On a crossed pair the original raw label c is well-defined
and the effective colours of BOTH structures are phi(c).
Thus equality of effective colours is literal, not just
congruence-equivalence, and no injectivity of f is needed.

This is the exact bridge for transporting local involution safety
from actual induced old safe-pair subgroups to the larger P.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {W : Type t} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Any original crossed pair retains its EXACT effective G-colour
in the induced raw pullback, even for non-injective f. -/
theorem pullbackRaw_effectiveReduct_crossColour
    (P : RawRectanglePresentation d V)
    (f : W → V) (x y : W)
    (hcross : ¬P.part (f x) (f y)) :
    (P.pullbackRaw f).effectiveReduct.F x y =
      P.effectiveReduct.F (f x) (f y) := by
  have hc : ∃ c : C, P.colour (f x) (f y) = some c := by
    cases h : P.colour (f x) (f y) with
    | none =>
        exact False.elim
          (hcross ((P.colour_none_iff (f x) (f y)).mp h))
    | some c =>
        exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hc
  have hcpull : (P.pullbackRaw f).colour x y = some c := hc
  exact ((P.pullbackRaw f).effectiveReduct_crossColour x y c hcpull).symm.trans
    (P.effectiveReduct_crossColour (f x) (f y) c hc)

/-- The exact induced old E relation is preserved by the canonical
effective reduct; neither direction changes a part. -/
theorem pullbackRaw_effectiveReduct_part_iff
    (P : RawRectanglePresentation d V)
    (f : W → V) (x y : W) :
    (P.pullbackRaw f).effectiveReduct.part x y ↔
      P.effectiveReduct.part (f x) (f y) := by
  exact ((P.pullbackRaw f).effectiveReduct_part x y).trans
    (P.effectiveReduct_part (f x) (f y)).symm

/-- Exact canonical effective colour of an induced raw embedding.
No injectivity of `f` is required here: preserving the Option-valued
raw colour on the image of every pair already gives literal equality
of effective G-colours on every originally crossed pair. -/
theorem effectiveReduct_crossColour_of_inducedRawColours
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W)
    (f : V → W)
    (hcolour : ∀ x y : V, Q.colour (f x) (f y) = P.colour x y)
    (x y : V) (hcross : ¬P.part x y) :
    Q.effectiveReduct.F (f x) (f y) = P.effectiveReduct.F x y := by
  cases hc : P.colour x y with
  | none =>
      exact False.elim
        (hcross ((P.colour_none_iff x y).mp hc))
  | some c =>
      have hQc : Q.colour (f x) (f y) = some c :=
        (hcolour x y).trans hc
      exact (Q.effectiveReduct_crossColour (f x) (f y) c hQc).symm.trans
        (P.effectiveReduct_crossColour x y c hc)

/-- Exact E-part agreement for an arbitrary induced raw embedding. -/
theorem effectiveReduct_part_iff_of_inducedRawPart
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W)
    (f : V → W)
    (hpart : ∀ x y : V, Q.part (f x) (f y) ↔ P.part x y)
    (x y : V) :
    Q.effectiveReduct.part (f x) (f y) ↔
      P.effectiveReduct.part x y :=
  (Q.effectiveReduct_part (f x) (f y)).trans
    ((hpart x y).trans (P.effectiveReduct_part x y).symm)

end RawRectanglePresentation
end SemigenericEPPA
