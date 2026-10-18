import SemigenericEPPA.Structure.RawCoverAutomorphisms
import SemigenericEPPA.Algebra.PrescribedRawCompatibility

/-!
# An actual raw-cover automorphism with ALL old residual valuations fixed

The previous lift theorem extended each effective base automorphism
to *some* automorphism of its fixed raw cover. For ordinary EPPA we
must prescribe the action on the complete residual valuation of
every old domain point.

Suppose S is a set of distinguished effective base vertices, and
etaSource(x,y), etaTarget(x,y) are their original and desired residual
coordinates. The prescribed action sends

     (x, etaSource(x,-)) ↦ (theta x, etaTarget(x,-))

for all x in S.  The only necessary compatibility condition says
that the raw residual labels on each old cross-edge x,y in S agree
before and after this action.

By the verified prescribed-correction completion (3.24),(3.28),
one correction family makes this happen on ALL coordinates while
preserving EVERY raw P_c relation on the SAME fixed cover.

This is the full relative raw-lift lemma modulo exact residual-label
equality. The next gate derives that equality from a raw partial
automorphism of the old structure and its section-encoded embedding.
No coherent group action is claimed.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {V : Type z} {d : RawDatum G C}

/-- The raw-cover automorphism extends the entire prescribed
old residual valuation at each domain vertex, not just the
effective base coordinate or the raw edge colour. -/
theorem exists_rawCoverAutomorphism_extending_old
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (theta : Equiv.Perm V)
    (hE : ∀ x y, D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y)
    (S : Set V)
    (etaSource etaTarget : V → V → L)
    (hlabel : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      rawResidual (etaTarget x (theta y))
          (etaTarget y (theta x)) (b (theta x) (theta y)) =
        rawResidual (etaSource x y) (etaSource y x) (b x y)) :
    ∃ T : RawCoverVertex V L ≃ RawCoverVertex V L,
      (∀ x : V, x ∈ S →
        T (x, etaSource x) = (theta x, etaTarget x)) ∧
      (∀ X Y : RawCoverVertex V L,
        D.part (T X).1 (T Y).1 ↔ D.part X.1 Y.1) ∧
      (∀ c : C, ∀ X Y : RawCoverVertex V L,
        rawRel (rawCoverPresentation D code b hb).toStructure c
            (T X) (T Y) ↔
          rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  obtain ⟨correction, hrow, hcorr⟩ :=
    exists_oldRawCorrectionExtension D code.shift b hb theta
      hE hF S etaSource etaTarget hlabel
  let T : RawCoverVertex V L ≃ RawCoverVertex V L :=
    rawCoverTransport theta correction
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    apply Prod.ext
    · rfl
    · funext y
      let u : V := theta.symm y
      have hcoord := rawCoverTransport_coord theta correction
        ((x, etaSource x) : RawCoverVertex V L) u
      have heval : (T (x, etaSource x)).2 y =
          etaSource x u + correction x u := by
        calc
          (T (x, etaSource x)).2 y =
            (T (x, etaSource x)).2 (theta u) := by
              rw [show theta u = y from theta.apply_symm_apply y]
          _ = etaSource x u + correction x u := hcoord
      calc
        (T (x, etaSource x)).2 y =
          etaSource x u + correction x u := heval
        _ = etaSource x u +
            (etaTarget x (theta u) - etaSource x u) := by
              rw [hrow x u hx]
        _ = etaTarget x (theta u) := by abel
        _ = etaTarget x y := by
              rw [theta.apply_symm_apply y]
  · intro X Y
    exact rawCoverTransport_part_iff D theta hE correction X Y
  · intro c X Y
    exact rawCoverTransport_rawRel_iff D code b hb theta hE hF
      correction hcorr c X Y

end SemigenericEPPA
