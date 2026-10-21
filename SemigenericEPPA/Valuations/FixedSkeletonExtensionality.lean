import SemigenericEPPA.Valuations.EffectiveCarrier

/-!
# Extensionality of fixed two-layer effective witness skeletons

The positive coherent nontrivial-G theorem must choose ONE witness
skeleton and old embedding BEFORE quantifying over all induced
substructures S and their finite automorphism groups H.

Several independently certified H-action construction APIs return
existentially a skeleton whose colour is the same already chosen
constant good element g0, potentially after H and S have been fixed.

A witness skeleton has precisely one data field, the matrix
  colour : Part → Part → G,
and one proof-valued affine reversal field. Extensionality and
proof irrelevance make a skeleton uniquely determined by its matrix.

Thus ANY later output skeleton which is globally constant g0 is
LITERALLY equal to the fixed constant skeleton prechosen before
S/H. This removes a subtle quantifier-order ambiguity; it does
not assert existence of an H-action, raw cover or coherent EPPA.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- Proof-irrelevant skeleton extensionality. In particular,
proofs of affine reversal compatibility introduce no new choices. -/
theorem EffectiveWitnessSkeleton.eq_of_colour_eq
    {D : EffectiveGeometry s V}
    (K L : EffectiveWitnessSkeleton D)
    (hColour : ∀ q r : EffectiveWitnessPart D,
      K.colour q r = L.colour q r) :
    K = L := by
  cases K with
  | mk k hk =>
    cases L with
    | mk l hl =>
      have heq : k = l := by
        funext q r
        exact hColour q r
      cases heq
      rfl

/-- Two later constructions with the same prechosen globally
constant good effective colour are the SAME skeleton. -/
theorem EffectiveWitnessSkeleton.eq_of_sameConstant
    {D : EffectiveGeometry s V}
    (K L : EffectiveWitnessSkeleton D)
    (g0 : G)
    (hK : ∀ q r : EffectiveWitnessPart D, K.colour q r = g0)
    (hL : ∀ q r : EffectiveWitnessPart D, L.colour q r = g0) :
    K = L := by
  apply K.eq_of_colour_eq L
  intro q r
  exact (hK q r).trans (hL q r).symm

end SemigenericEPPA
