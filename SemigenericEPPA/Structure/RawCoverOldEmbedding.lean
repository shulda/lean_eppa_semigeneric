import SemigenericEPPA.Algebra.ResidualOldCoordinates
import SemigenericEPPA.Structure.RawCover
import Mathlib.Data.Fintype.EquivFin

/-!
# Embedding a prescribed old raw structure into the fixed raw cover

Suppose an old literal raw rectangle presentation A embeds into the
effective base D by an injection e respecting E. For each ordered old
cross-edge x,y, suppose ell(x,y) is an additive residual label:
* its affine reversal agrees with the chosen baseline shift;
* decoding ell(x,y) in the raw fibre over F(e x,e y) gives exactly
  the originally prescribed colour of (x,y).

The oriented-pair interpolation theorem (3.27) constructs a residual
valuation eta_x on the WHOLE effective base for each old vertex x.
Embedding x ↦ (e x,eta_x) then preserves and reflects E and EVERY
raw colour P_c literally, not just the effective group colour.

This is a conditional theorem: later we obtain ell(x,y) from the
sections of a finite affine residual code (3.26). No EPPA or
automorphism extension is presumed.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t

variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- The actual old raw vertex, including its explicit complete
residual valuation on the effective base. -/
noncomputable def rawCoverOldMap
    [LinearOrder U]
    (e : U → V) (he : Function.Injective e)
    (b : V → V → L) (ell : U → U → L)
    (x : U) : RawCoverVertex V L :=
  (e x, oldResidualValuation e he b ell x)

@[simp] theorem rawCoverOldMap_base
    [LinearOrder U]
    (e : U → V) (he : Function.Injective e)
    (b : V → V → L) (ell : U → U → L)
    (x : U) :
    (rawCoverOldMap e he b ell x).1 = e x := rfl

theorem rawCoverOldMap_injective
    [LinearOrder U]
    (e : U → V) (he : Function.Injective e)
    (b : V → V → L) (ell : U → U → L) :
    Function.Injective (rawCoverOldMap e he b ell) := by
  intro x y h
  exact he (congrArg Prod.fst h)

/-- All raw colours of the old structure are reproduced exactly
under the chosen oriented residual valuations, including reversal. -/
theorem rawCoverOldMap_colour
    [LinearOrder U]
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V) (he : Function.Injective e)
    (hpart : ∀ x y, D.part (e x) (e y) ↔ P.part x y)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (ell : U → U → L)
    (hell : ∀ x y, ¬P.part x y →
      ell y x = code.shift (D.F (e x) (e y)) - ell x y)
    (hdecode : ∀ x y c, P.colour x y = some c →
      (code.decode (D.F (e x) (e y)) (ell x y)).val = c)
    (x y : U) :
    rawCoverColour D code b
      (rawCoverOldMap e he b ell x)
      (rawCoverOldMap e he b ell y) = P.colour x y := by
  classical
  by_cases hxy : P.part x y
  · have hbase : D.part (e x) (e y) := (hpart x y).2 hxy
    have hsame :=
      rawCoverColour_same D code b
        (rawCoverOldMap e he b ell x)
        (rawCoverOldMap e he b ell y) hbase
    rw [hsame, (P.colour_none_iff x y).2 hxy]
  · have hbase : ¬D.part (e x) (e y) := by
      intro h
      exact hxy ((hpart x y).1 h)
    have hellBase : ∀ a b : U, ¬D.part (e a) (e b) →
        ell b a = code.shift (D.F (e a) (e b)) - ell a b := by
      intro a b hab
      apply hell a b
      intro hh
      exact hab ((hpart a b).2 hh)
    have hval := oldResidualValuation_recovers D e he code.shift
      b ell hb hellBase x y hbase
    cases hcol : P.colour x y with
    | none =>
      exact False.elim (hxy ((P.colour_none_iff x y).1 hcol))
    | some c =>
      have hspec := hdecode x y c hcol
      change rawCoverColour D code b
        (rawCoverOldMap e he b ell x)
        (rawCoverOldMap e he b ell y) = some c
      change (if D.part (e x) (e y) then none
        else some (code.decode (D.F (e x) (e y))
          (rawResidual
            (oldResidualValuation e he b ell x (e y))
            (oldResidualValuation e he b ell y (e x))
            (b (e x) (e y)))).val) = some c
      rw [if_neg hbase, hval]
      exact congrArg Option.some hspec

/-- A true old raw induced substructure on a finite carrier embeds
into the fixed raw-fibre cover, conditional on exact encoded edge
labels ell. The auxiliary order on the old carrier is not added to
its relational language. -/
theorem exists_rawCoverOldEmbedding
    [Finite U]
    (P : RawRectanglePresentation d U)
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (e : U → V) (he : Function.Injective e)
    (hpart : ∀ x y, D.part (e x) (e y) ↔ P.part x y)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (ell : U → U → L)
    (hell : ∀ x y, ¬P.part x y →
      ell y x = code.shift (D.F (e x) (e y)) - ell x y)
    (hdecode : ∀ x y c, P.colour x y = some c →
      (code.decode (D.F (e x) (e y)) (ell x y)).val = c) :
    ∃ ψ : U → RawCoverVertex V L,
      Function.Injective ψ ∧
      (∀ x y, D.part (ψ x).1 (ψ y).1 ↔ P.part x y) ∧
      (∀ c : C, ∀ x y,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (ψ x) (ψ y) ↔
        rawRel P.toStructure c x y) := by
  classical
  letI : Fintype U := Fintype.ofFinite _
  letI : LinearOrder U :=
    LinearOrder.lift' (Fintype.equivFin U) (Fintype.equivFin U).injective
  let ψ : U → RawCoverVertex V L := rawCoverOldMap e he b ell
  refine ⟨ψ, rawCoverOldMap_injective e he b ell, ?_, ?_⟩
  · intro x y
    exact hpart x y
  · intro c x y
    change rawCoverColour D code b (ψ x) (ψ y) = some c ↔
      P.colour x y = some c
    rw [rawCoverOldMap_colour P D code e he hpart b hb ell
      hell hdecode x y]

end SemigenericEPPA
