import SemigenericEPPA.Structure.RawCover
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import SemigenericEPPA.Structure.TotalOldRawPalette
import SemigenericEPPA.Algebra.AffineResidualGlobalEncoder

/-!
# Exact old raw substructure on the zero section of one fixed cover

The previously verified general raw EPPA witness uses possibly
nonzero vertex residual valuations to encode the original raw
colours. The positive coherent construction instead requires the
same old embedding to be the ZERO section of one globally fixed
raw cover.

Given any old effective embedding e:U↪V and a single affine baseline
b encoding the literal old raw colours on old-old cross E-pairs,
the zero-section map x↦(e x, 0) is an exact induced raw embedding.

The code.encodeRaw sections and decode_encode identity certify
the entire original ordered raw colouring, with no assumption
that its fibres are singleton or have self-reversing colours.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- The literal old zero-section map used simultaneously by
individual extensions and homomorphic stabilizer lifts. -/
def rawCoverZeroOldMap
    (e : U → V) (L : Type w) [Zero L] (x : U) :
    RawCoverVertex V L :=
  (e x, fun _ => 0)

/-- Exact recovery of ALL old raw colours at the chosen zero section
from the canonical encoded old-old affine baseline. -/
theorem rawCoverZeroOldMap_colour
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (e : U → V)
    (hpart : ∀ x y, D.part (e x) (e y) ↔ P.part x y)
    (hF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y))
    (hBOld : ∀ x y, ¬P.part x y →
      b (e x) (e y) = code.encodeRaw (P.totalOldRawColour x y))
    (x y : U) :
    rawCoverColour D code b
        (rawCoverZeroOldMap e L x)
        (rawCoverZeroOldMap e L y) =
      P.colour x y := by
  classical
  by_cases hp : P.part x y
  · have hbase : D.part (e x) (e y) := (hpart x y).mpr hp
    rw [rawCoverColour_same D code b _ _ hbase,
      (P.colour_none_iff x y).mpr hp]
  · have hbase : ¬D.part (e x) (e y) := by
      intro he
      exact hp ((hpart x y).mp he)
    have hcolour := P.totalOldRawColour_cross x y hp
    have hphi : d.phi (P.totalOldRawColour x y) =
        D.F (e x) (e y) := hF x y _ hcolour
    have hdecode :
        (code.decode (D.F (e x) (e y))
          (code.encodeRaw (P.totalOldRawColour x y))).val =
        P.totalOldRawColour x y := by
      rw [← code.encode_of_projection (P.totalOldRawColour x y)
        (D.F (e x) (e y)) hphi]
      exact congrArg Subtype.val
        (code.decode_encode (D.F (e x) (e y))
          ⟨P.totalOldRawColour x y, hphi⟩)
    change rawCoverColour D code b
      (e x, fun _ : V => (0 : L))
      (e y, fun _ : V => (0 : L)) = P.colour x y
    rw [hcolour]
    simp [rawCoverColour, hbase, rawResidual, hBOld x y hp,
      hdecode]

/-- The zero-section old embedding is injective and reflects E
as soon as its underlying effective old map does. -/
theorem rawCoverZeroOldMap_injective
    (e : U → V) (he : Function.Injective e) :
    Function.Injective (rawCoverZeroOldMap e L) := by
  intro x y h
  exact he (congrArg Prod.fst h)

/-- Old E-parts are reproduced without mergers, using the exact
underlying effective embedding. -/
theorem rawCoverZeroOldMap_part
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (e : U → V)
    (hpart : ∀ x y, D.part (e x) (e y) ↔ P.part x y)
    (x y : U) :
    D.part (rawCoverZeroOldMap e L x).1
      (rawCoverZeroOldMap e L y).1 ↔ P.part x y :=
  hpart x y

end SemigenericEPPA
