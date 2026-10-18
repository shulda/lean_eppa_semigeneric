import SemigenericEPPA.Algebra.AffineResidualCode
import SemigenericEPPA.Structure.RawPresentation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# The actual finite raw-fibre cover, conditional on a residual code

Given an effective group-valued rectangle geometry D, a common
additive residual coefficient group L, an affine code with typed
decoders pi_g:L -> C_g satisfying (3.20), and a baseline satisfying
(3.21), form vertices (X,eta) with eta:Y -> L.

On a genuine cross-part pair define
  ell((X,eta),(Y,zeta)) = eta(Y) - zeta(X) + b(X,Y),
  colour = pi_(F(X,Y))(ell).
This is exactly the manuscript's (3.22)--(3.23), with extra dummy
same-part coordinates in eta (harmless for the construction).

We prove the actual R1--R3 axioms in the literal AllThoseEPPA
rectangle language, not merely an effective pullback candidate:
the E setoid pulls back from D, raw colours reverse correctly under
the affine involution, and their effective image is the original F,
so every noncommutative rectangle law is preserved. The cover has a
finite carrier whenever V and L are finite.

This is conditional on the affine residual code, whose existence
for arbitrary finite d remains the separate R0 gate. Embedding a
prescribed raw A and lifting automorphisms of D are separate R1 gates.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {V : Type z}
variable {d : RawDatum G C}

/-- One real base vertex with a full residual function; the
coordinates toward vertices in the same E-part are unused. -/
abbrev RawCoverVertex (V : Type z) (L : Type w) :=
  V × (V → L)

/-- The exact raw colour from the additive difference of two residual
valuation coordinates and the chosen affine baseline. -/
noncomputable def rawCoverColour
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (X Y : RawCoverVertex V L) : Option C := by
  classical
  exact if D.part X.1 Y.1 then none
    else some (code.decode (D.F X.1 Y.1)
      (rawResidual (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1))).val

theorem rawCoverColour_none_iff
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (X Y : RawCoverVertex V L) :
    rawCoverColour D code b X Y = none ↔ D.part X.1 Y.1 := by
  classical
  by_cases h : D.part X.1 Y.1
  · simp [rawCoverColour, h]
  · simp [rawCoverColour, h]

theorem rawCoverColour_same
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (X Y : RawCoverVertex V L)
    (h : D.part X.1 Y.1) :
    rawCoverColour D code b X Y = none :=
  (rawCoverColour_none_iff D code b X Y).2 h

/-- A raw colour is always in the *exact* fibre over the effective
group colour of the two underlying base vertices. -/
theorem rawCoverColour_phi
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (X Y : RawCoverVertex V L)
    (hxy : ¬D.part X.1 Y.1)
    (c : C) (hc : rawCoverColour D code b X Y = some c) :
    d.phi c = D.F X.1 Y.1 := by
  classical
  have heq :
      (code.decode (D.F X.1 Y.1)
        (rawResidual (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1))).val = c := by
    have hs : some (code.decode (D.F X.1 Y.1)
        (rawResidual (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1))).val =
          some c := by
      simpa only [rawCoverColour, if_neg hxy] using hc
    exact Option.some.inj hs
  rw [← heq]
  exact code.decode_phi _ _

/-- Actual reversal of the complete raw colouring, via the affine
residual involution rho_g(l)=shift(g)-l. This works even when s(g)=g
and the raw fibre has no self-reversing colour. -/
theorem rawCoverColour_reverse
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (X Y : RawCoverVertex V L) :
    rawCoverColour D code b Y X =
      Option.map d.reverse (rawCoverColour D code b X Y) := by
  classical
  by_cases hxy : D.part X.1 Y.1
  · have hyx : D.part Y.1 X.1 := D.part.iseqv.symm hxy
    simp [rawCoverColour, hxy, hyx]
  · have hyx : ¬D.part Y.1 X.1 := by
      intro h
      exact hxy (D.part.iseqv.symm h)
    have hres :
        rawResidual (Y.2 X.1) (X.2 Y.1) (b Y.1 X.1) =
          code.shift (D.F X.1 Y.1) -
            rawResidual (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1) :=
      rawResidual_reverse (code.shift (D.F X.1 Y.1))
        (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1) (b Y.1 X.1)
        (hb X.1 Y.1 hxy)
    have hdec :
        (code.decode (D.F Y.1 X.1)
          (rawResidual (Y.2 X.1) (X.2 Y.1) (b Y.1 X.1))).val =
          d.reverse
            (code.decode (D.F X.1 Y.1)
              (rawResidual (X.2 Y.1) (Y.2 X.1)
                (b X.1 Y.1))).val := by
      rw [D.reverse_cross X.1 Y.1 hxy, hres]
      exact code.decode_reverse_val _ _
    simp only [rawCoverColour, if_neg hyx, if_neg hxy, Option.map_some]
    exact congrArg Option.some hdec

/-- Literal R1--R3 raw structure on the complete residual cover.
The effective F of every raw cross edge is the group colour of its
two base points, and all rectangles are inherited from D. -/
noncomputable def rawCoverPresentation
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y) :
    RawRectanglePresentation d (RawCoverVertex V L) where
  part := fun X Y => D.part X.1 Y.1
  part_equiv := by
    constructor
    · intro X
      exact D.part.iseqv.refl X.1
    · intro X Y h
      exact D.part.iseqv.symm h
    · intro X Y Z hXY hYZ
      exact D.part.iseqv.trans hXY hYZ
  colour := rawCoverColour D code b
  colour_none_iff := rawCoverColour_none_iff D code b
  colour_reverse := rawCoverColour_reverse D code b hb
  rectangle := by
    intro x₀ x₁ y₀ y₁ hx hy c₀₀ c₀₁ c₁₀ c₁₁
      h00 h01 h10 h11
    have hcross : ¬D.part x₀.1 y₀.1 := by
      intro h
      have hn := rawCoverColour_same D code b x₀ y₀ h
      rw [h00] at hn
      cases hn
    obtain ⟨h01c, h10c, h11c⟩ :=
      D.cross_square x₀.1 x₁.1 y₀.1 y₁.1 hx hy hcross
    have he00 := rawCoverColour_phi D code b x₀ y₀ hcross c₀₀ h00
    have he01 := rawCoverColour_phi D code b x₀ y₁ h01c c₀₁ h01
    have he10 := rawCoverColour_phi D code b x₁ y₀ h10c c₁₀ h10
    have he11 := rawCoverColour_phi D code b x₁ y₁ h11c c₁₁ h11
    rw [he00, he01, he10, he11]
    exact D.rectangle x₀.1 x₁.1 y₀.1 y₁.1 hx hy hcross

/-- The residual cover is an actual member of the exact relational
class K(G,s,phi), conditional only on the residual code and baseline. -/
theorem rawCover_isRectangleStructure
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y) :
    IsRectangleStructure d (rawCoverPresentation D code b hb).toStructure :=
  (rawCoverPresentation D code b hb).toStructure_isRectangleStructure

/-- Finite coefficient group and finite base ensure that the whole
unrestricted residual valuation cover has finite vertex set. -/
theorem finite_rawCoverVertices [Finite V] [Finite L] :
    Finite (RawCoverVertex V L) := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype L := Fintype.ofFinite _
  infer_instance

end SemigenericEPPA
