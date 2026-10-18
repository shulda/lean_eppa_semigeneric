import SemigenericEPPA.Structure.RawCoverEncodedOld
import SemigenericEPPA.Structure.RawCoverLiftAlongEmbedding
import Mathlib.Data.Fintype.EquivFin

/-!
# One section-based old raw embedding with all relative raw lifts

Fix an effective E/F rectangle geometry D and an induced effective
embedding e of a finite old raw structure P. Choose ONE baseline and
ONE affine residual code, independently of any partial map p.

The old residual edge labels are the canonical section encodings
ell(x,y) from (3.26). The oriented-pair interpolation (3.27)
constructs eta_x on the entire effective base for each old vertex.
Extend x↦eta_x along the injection e, assigning zero to unused
base vertices. The resulting old raw embedding
  psi(x)=(e x,eta_{e x})
preserves and reflects every original raw P_c predicate.

For EVERY old partial raw map p preserving literal raw colours,
whenever an effective automorphism theta extends its old effective
action, the same fixed raw cover has a raw automorphism T extending
p on the COMPLETE old raw valuation vertices. The compatibility
of prescribed corrections is automatic because the canonical
section residual label depends only on the original raw colour.

This is precisely the raw-cover lemma's old-embedding and relative
lifting parts (iii)--(iv), CONDITIONAL only on the affine residual
code and the chosen effective automorphism theta. It does not yet
assert the full unconditional raw EPPA theorem.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- One old raw substructure embedding works for all old partial
raw maps whose effective actions extend. The witness cover and psi
are selected BEFORE choosing p or theta. -/
theorem exists_sectionRawCoverEmbedding_withLifts
    [Finite U] [Finite V] [Finite L]
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
    Finite (RawCoverVertex V L) ∧
    ∃ ψ : U → RawCoverVertex V L,
      Function.Injective ψ ∧
      (∀ x y, D.part (ψ x).1 (ψ y).1 ↔ P.part x y) ∧
      (∀ c : C, ∀ x y,
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (ψ x) (ψ y) ↔ rawRel P.toStructure c x y) ∧
      (∀ (S : Set U) (p : S → U)
          (theta : Equiv.Perm V),
        (∀ x y : S,
          P.colour (p x) (p y) = P.colour x.val y.val) →
        (∀ x : S, theta (e x.val) = e (p x)) →
        (∀ x y, D.part (theta x) (theta y) ↔ D.part x y) →
        (∀ x y, ¬D.part x y →
          D.F (theta x) (theta y) = D.F x y) →
        ∃ T : RawCoverVertex V L ≃ RawCoverVertex V L,
          (∀ x : S, T (ψ x.val) = ψ (p x)) ∧
          (∀ X Y : RawCoverVertex V L,
            D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
          (∀ c : C, ∀ X Y : RawCoverVertex V L,
            rawRel (rawCoverPresentation D code b hb).toStructure c
              (T X) (T Y) ↔
            rawRel (rawCoverPresentation D code b hb).toStructure c X Y)) := by
  classical
  letI : Fintype U := Fintype.ofFinite _
  letI : LinearOrder U :=
    LinearOrder.lift' (Fintype.equivFin U)
      (Fintype.equivFin U).injective
  let ell : U → U → L := encodedOldRawResidual P D code e hF
  let etaOld : U → V → L := oldResidualValuation e he b ell
  let eta : V → V → L :=
    extendResidualAlongInjection e he etaOld
  have heta (x : U) : eta (e x) = etaOld x :=
    extendResidualAlongInjection_apply e he etaOld x
  have hell : ∀ x y : U, ¬D.part (e x) (e y) →
      ell y x = code.shift (D.F (e x) (e y)) - ell x y := by
    intro x y hcross
    exact encodedOldRawResidual_reverse P D code e hpart hF
      x y (by
        intro h
        exact hcross ((hpart x y).2 h))
  have hrec (x y : U) (hcross : ¬D.part (e x) (e y)) :
      rawResidual (eta (e x) (e y))
          (eta (e y) (e x)) (b (e x) (e y)) = ell x y := by
    rw [heta x, heta y]
    exact oldResidualValuation_recovers D e he code.shift
      b ell hb hell x y hcross
  let ψ : U → RawCoverVertex V L := fun x => (e x, eta (e x))
  have hψinjective : Function.Injective ψ := by
    intro x y hxy
    exact he (congrArg Prod.fst hxy)
  have hψcolour (x y : U) :
      rawCoverColour D code b (ψ x) (ψ y) = P.colour x y := by
    have hc := rawCoverOldMap_colour P D code e he hpart
      b hb ell
      (encodedOldRawResidual_reverse P D code e hpart hF)
      (encodedOldRawResidual_decode P D code e hF) x y
    simpa only [ψ, rawCoverOldMap, etaOld, heta] using hc
  refine ⟨finite_rawCoverVertices, ψ, hψinjective, ?_, ?_, ?_⟩
  · intro x y
    exact hpart x y
  · intro c x y
    change rawCoverColour D code b (ψ x) (ψ y) = some c ↔
      P.colour x y = some c
    rw [hψcolour x y]
  · intro S p theta hraw hext hEθ hFθ
    have hlabel (x y : S) (hcross : ¬D.part (e x.val) (e y.val)) :
        rawResidual
          (eta (e (p x)) (e (p y)))
          (eta (e (p y)) (e (p x)))
          (b (e (p x)) (e (p y))) =
        rawResidual
          (eta (e x.val) (e y.val))
          (eta (e y.val) (e x.val))
          (b (e x.val) (e y.val)) := by
      have htarget : ¬D.part (e (p x)) (e (p y)) := by
        intro ht
        apply hcross
        have htheta :
            D.part (theta (e x.val)) (theta (e y.val)) := by
          simpa only [hext x, hext y] using ht
        exact (hEθ _ _).mp htheta
      calc
        rawResidual
            (eta (e (p x)) (e (p y)))
            (eta (e (p y)) (e (p x)))
            (b (e (p x)) (e (p y))) =
          ell (p x) (p y) := hrec (p x) (p y) htarget
        _ = ell x.val y.val :=
          encodedOldRawResidual_of_equalColour P D code e hF
            (p x) (p y) x.val y.val (hraw x y)
        _ = rawResidual
            (eta (e x.val) (e y.val))
            (eta (e y.val) (e x.val))
            (b (e x.val) (e y.val)) :=
          (hrec x.val y.val hcross).symm
    obtain ⟨T, hT, hTE, hTc⟩ :=
      exists_rawCoverLift_alongEmbedding
        D code b hb e he eta S p theta hEθ hFθ hext hlabel
    exact ⟨T, hT, hTE, hTc⟩

end SemigenericEPPA
