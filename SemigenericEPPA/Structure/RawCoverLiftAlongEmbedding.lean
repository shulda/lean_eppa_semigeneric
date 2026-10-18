import SemigenericEPPA.Structure.RawCoverPartialResidualLift

/-!
# Partial raw-cover extension along the old effective embedding

An old raw structure U sits inside the effective witness carrier V
through an injective map e. Its partial automorphism p:S→U
is extended by an effective automorphism theta of V.

The source domain in the raw-cover lift is the IMAGE e(S), not
an incorrectly identified subtype of V. Since theta extends p,
the desired map on e(S) is just the restriction of theta.

Assume a fixed family eta:V→(V→L) of residual vertex valuations
has canonical residual labels that p preserves on old cross edges.
Then the checked raw-cover lift transports the complete old
raw-cover points (e x,eta(e x)) to (e(p x),eta(e(p x))).

The theorem eliminates the need to separately specify a padded
partial map or target residual valuations on the effective base.
To close ordinary raw EPPA, eta will be chosen from the section-based
old embedding and the residual-label hypothesis will follow from
preservation of the literal old raw colours.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z t
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {U : Type z} {V : Type t}
variable {d : RawDatum G C}

/-- An effective automorphism extending a partial old map also has a
raw-cover automorphism extending that map on the entire chosen
old raw valuation vertices, provided their canonical residual
labels are preserved. -/
theorem exists_rawCoverLift_alongEmbedding
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (e : U → V) (he : Function.Injective e)
    (eta : V → V → L)
    (S : Set U) (p : S → U)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (hext : ∀ x : S, theta (e x.val) = e (p x))
    (hlabel : ∀ x y : S, ¬D.part (e x.val) (e y.val) →
      rawResidual
          (eta (e (p x)) (e (p y)))
          (eta (e (p y)) (e (p x)))
          (b (e (p x)) (e (p y))) =
        rawResidual
          (eta (e x.val) (e y.val))
          (eta (e y.val) (e x.val))
          (b (e x.val) (e y.val))) :
    ∃ T : RawCoverVertex V L ≃ RawCoverVertex V L,
      (∀ x : S,
        T (e x.val, eta (e x.val)) =
          (e (p x), eta (e (p x)))) ∧
      (∀ X Y : RawCoverVertex V L,
        D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c (T X) (T Y) ↔
          rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  let W : Set V := {z | ∃ x : S, e x.val = z}
  let pW : W → V := fun z => theta z.val
  have hlabelW :
      ∀ x y : W, ¬D.part x.val y.val →
        rawResidual (eta (pW x) (pW y))
            (eta (pW y) (pW x))
            (b (pW x) (pW y)) =
          rawResidual (eta x.val y.val) (eta y.val x.val)
            (b x.val y.val) := by
    intro x y hxy
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨bOld, hbOld⟩ := y.property
    have hcross : ¬D.part (e a.val) (e bOld.val) := by
      rw [ha, hbOld]
      exact hxy
    have h := hlabel a bOld hcross
    change rawResidual
        (eta (theta x.val) (theta y.val))
        (eta (theta y.val) (theta x.val))
        (b (theta x.val) (theta y.val)) =
      rawResidual (eta x.val y.val) (eta y.val x.val)
        (b x.val y.val)
    calc
      rawResidual
          (eta (theta x.val) (theta y.val))
          (eta (theta y.val) (theta x.val))
          (b (theta x.val) (theta y.val)) =
        rawResidual
          (eta (e (p a)) (e (p bOld)))
          (eta (e (p bOld)) (e (p a)))
          (b (e (p a)) (e (p bOld))) := by
            rw [← ha, ← hbOld, hext a, hext bOld]
      _ = rawResidual
          (eta (e a.val) (e bOld.val))
          (eta (e bOld.val) (e a.val))
          (b (e a.val) (e bOld.val)) := h
      _ = rawResidual (eta x.val y.val) (eta y.val x.val)
          (b x.val y.val) := by rw [ha, hbOld]
  obtain ⟨T, hmap, hpart, hcolour⟩ :=
    exists_rawCoverLift_of_partialResidualMap
      D code b hb eta W pW theta hE hF (by intro _; rfl)
      (fun x y hxy => hlabelW x y hxy)
  refine ⟨T, ?_, hpart, hcolour⟩
  intro x
  let y : W := ⟨e x.val, ⟨x, rfl⟩⟩
  have hy := hmap y
  change T (e x.val, eta (e x.val)) =
    (theta (e x.val), eta (theta (e x.val))) at hy
  simpa only [hext x] using hy

end SemigenericEPPA
