import SemigenericEPPA.Structure.RawCoverLiftAlongEmbedding
import SemigenericEPPA.Algebra.AffineResidualGlobalEncoder

/-!
# Individual partial raw lifts for a prechosen zero-section embedding

The positive coherent-EPPA fixed-cover construction embeds every old
vertex x as (e x,0) in the raw residual cover. A priori, the ordinary
raw EPPA embedding theorem uses nonzero residual valuations and does
NOT certify EPPA for this same zero-section embedding.

We close precisely this compatibility gap. Assume the already fixed
affine baseline b agrees on old-old cross E-pairs with the canonical
encoding code.encodeRaw(old x y). Then every effective automorphism
theta extending a partial old map which preserves these old raw
colours has an individual raw-cover lift extending the SAME old
zero-section embedding. The effective automorphism may be selected
independently for each partial map. No global coherent choice is
asserted here.

The raw cover, its baseline and zero-section embedding are all
chosen BEFORE the partial map.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- The SAME prechosen affine raw-cover zero section supports an
individual lift of each old partial map preserving literal old
cross-edge colours, provided an effective base automorphism
extends the map. -/
theorem exists_rawCoverZeroSectionLift_alongEmbedding
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (e : U → V) (he : Function.Injective e)
    (old : U → U → C)
    (hbOld : ∀ x y : U, ¬D.part (e x) (e y) →
      b (e x) (e y) = code.encodeRaw (old x y))
    (S : Set U) (p : S → U)
    (theta : Equiv.Perm V)
    (hOld : ∀ x y : S, ¬D.part (e x.val) (e y.val) →
      old (p x) (p y) = old x.val y.val)
    (hext : ∀ x : S, theta (e x.val) = e (p x))
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y) :
    ∃ T : Equiv.Perm (RawCoverVertex V L),
      (∀ x : S,
        T (e x.val, fun _ : V => (0 : L)) =
          (e (p x), fun _ : V => (0 : L))) ∧
      (∀ X Y : RawCoverVertex V L,
        D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ (c : C) (X Y : RawCoverVertex V L),
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (T X) (T Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  have hlabel : ∀ x y : S, ¬D.part (e x.val) (e y.val) →
      rawResidual
          ((fun _ : V => (0 : L)) (e (p y)))
          ((fun _ : V => (0 : L)) (e (p x)))
          (b (e (p x)) (e (p y))) =
        rawResidual
          ((fun _ : V => (0 : L)) (e y.val))
          ((fun _ : V => (0 : L)) (e x.val))
          (b (e x.val) (e y.val)) := by
    intro x y hcross
    have hcross' : ¬D.part (e (p x)) (e (p y)) := by
      intro hpart
      apply hcross
      exact (hE (e x.val) (e y.val)).mp (by
        simpa only [hext x, hext y] using hpart)
    have hbaseline :
        b (e (p x)) (e (p y)) =
          b (e x.val) (e y.val) := by
      calc
        b (e (p x)) (e (p y)) =
            code.encodeRaw (old (p x) (p y)) :=
          hbOld (p x) (p y) hcross'
        _ = code.encodeRaw (old x.val y.val) :=
          congrArg code.encodeRaw (hOld x y hcross)
        _ = b (e x.val) (e y.val) :=
          (hbOld x.val y.val hcross).symm
    simpa [rawResidual] using hbaseline
  obtain ⟨T, hOldT, hPartT, hRawT⟩ :=
    exists_rawCoverLift_alongEmbedding
      D code b hb e he
      (fun _ _ => (0 : L)) S p theta hE hF hext hlabel
  exact ⟨T, hOldT, hPartT, hRawT⟩

end SemigenericEPPA
