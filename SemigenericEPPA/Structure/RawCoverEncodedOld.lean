import SemigenericEPPA.Structure.RawCoverOldEmbedding

/-!
# Sections of the residual code supply every prescribed old raw label

The interpolating old embedding previously required an abstract
residual label ell(x,y) which (a) reverses affinely and (b) decodes
to the original raw colour.  Such labels are not additional data.

Given the raw old structure A, its effective embedding e into
the fixed effective base D, and ANY affine residual code, define

  ell(x,y) = sigma_(F(e x,e y))(colour_A(x,y))

on each old cross-part pair, using exactly the typed section from
(3.20). It is zero on same-part pairs. The two section axioms
imply its correct affine reversal and literal raw decoding.

Combined with the checked oriented coordinate interpolation (3.27)
and raw-cover presentation, this produces a true induced raw
embedding above the given effective embedding e, with NO extra
choice of residual labels. This is part (iii) of the manuscript's
raw-cover lemma, conditional only on the finite affine code.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t

variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- Old raw colour encoded by the section in the exact effective
fibre, or a harmless zero on a same-part pair. -/
noncomputable def encodedOldRawResidual
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V)
    (hF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y))
    (x y : U) : L := by
  classical
  exact match hc : P.colour x y with
  | none => 0
  | some c =>
      code.encode (D.F (e x) (e y)) ⟨c, hF x y c hc⟩

/-- When an actual old cross edge has colour c, its encoded
residual label is EXACTLY the prescribed section of c. -/
theorem encodedOldRawResidual_ofColour
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V)
    (hF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y))
    (x y : U) (c : C)
    (hc : P.colour x y = some c) :
    encodedOldRawResidual P D code e hF x y =
      code.encode (D.F (e x) (e y)) ⟨c, hF x y c hc⟩ := by
  classical
  simp [encodedOldRawResidual, hc]

/-- The encoded old labels always reverse by the correct
nontrivial affine shift. This works when the raw fibre over an
s-fixed effective colour contains NO reversal-fixed raw colour. -/
theorem encodedOldRawResidual_reverse
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V)
    (hpart : ∀ x y, D.part (e x) (e y) ↔ P.part x y)
    (hF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y))
    (x y : U) (hxy : ¬P.part x y) :
    encodedOldRawResidual P D code e hF y x =
      code.shift (D.F (e x) (e y)) -
        encodedOldRawResidual P D code e hF x y := by
  have hcross : ¬D.part (e x) (e y) := by
    intro h
    exact hxy ((hpart x y).mp h)
  obtain ⟨c, hc⟩ : ∃ c : C, P.colour x y = some c := by
    cases h : P.colour x y with
    | none =>
        exact False.elim (hxy ((P.colour_none_iff x y).mp h))
    | some c => exact ⟨c, h⟩
  have hrc : P.colour y x = some (d.reverse c) := by
    rw [P.colour_reverse x y, hc]
    rfl
  let cF : d.fibre (D.F (e x) (e y)) :=
    ⟨c, hF x y c hc⟩
  calc
    encodedOldRawResidual P D code e hF y x =
      code.encode (D.F (e y) (e x))
        ⟨d.reverse c, hF y x (d.reverse c) hrc⟩ :=
          encodedOldRawResidual_ofColour P D code e hF y x
            (d.reverse c) hrc
    _ = code.encode (d.s (D.F (e x) (e y)))
        (d.reverseFibre (D.F (e x) (e y)) cF) := by
          rw [D.reverse_cross (e x) (e y) hcross]
          rfl
    _ = code.shift (D.F (e x) (e y)) -
        code.encode (D.F (e x) (e y)) cF :=
          code.encode_reverse _ cF
    _ = code.shift (D.F (e x) (e y)) -
        encodedOldRawResidual P D code e hF x y := by
          rw [encodedOldRawResidual_ofColour P D code e hF x y c hc]

/-- Decoding the section-defined residual label recovers every
old raw colour LITERALLY, not just after applying phi. -/
theorem encodedOldRawResidual_decode
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V)
    (hF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y))
    (x y : U) (c : C) (hc : P.colour x y = some c) :
    (code.decode (D.F (e x) (e y))
      (encodedOldRawResidual P D code e hF x y)).val = c := by
  rw [encodedOldRawResidual_ofColour P D code e hF x y c hc]
  exact congrArg Subtype.val
    (code.decode_encode (D.F (e x) (e y))
      ⟨c, hF x y c hc⟩)

/-- Genuine literal raw induced embedding above ANY given injective
effective embedding of a finite old raw presentation, conditional
only on an affine residual code and baseline. Both E and every
raw P_c are reflected as well as preserved. -/
theorem exists_rawCoverOldEmbedding_of_effective
    [Finite U]
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V) (he : Function.Injective e)
    (hpart : ∀ x y, D.part (e x) (e y) ↔ P.part x y)
    (hF : ∀ x y c, P.colour x y = some c →
      d.phi c = D.F (e x) (e y))
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y) :
    ∃ ψ : U → RawCoverVertex V L,
      Function.Injective ψ ∧
      (∀ x y, D.part (ψ x).1 (ψ y).1 ↔ P.part x y) ∧
      (∀ c : C, ∀ x y,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (ψ x) (ψ y) ↔ rawRel P.toStructure c x y) := by
  let ell : U → U → L := encodedOldRawResidual P D code e hF
  exact exists_rawCoverOldEmbedding
    P D code e he hpart b hb ell
    (encodedOldRawResidual_reverse P D code e hpart hF)
    (encodedOldRawResidual_decode P D code e hF)

end SemigenericEPPA
