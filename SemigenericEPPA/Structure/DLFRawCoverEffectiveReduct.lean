import SemigenericEPPA.Structure.RawPresentationEffectiveBridge
import SemigenericEPPA.Structure.RawCover

/-!
# The actual raw fibre cover has precisely its advertised effective reduct

The relative DLF construction chooses ONE finite raw cover over a
phase-expanded group-valued rectangle geometry D. Its safety
condition on H-involutions is naturally expressed using the
effective colour of the actual original-language raw cover,
not an unrelated auxiliary group-valued colouring.

We prove these colours agree LITERALLY on every cross-E pair:
    F_(rawCover(D,code,b)).effectiveReduct (X,Y) = D.F(X.base,Y.base).

This equality needs no congruence saturation, affine normalisation,
raw palette cardinality assumption, or choice of a special fibre
section: it follows only from exact typed decoding and the
already certified canonical effective-reduct bridge.

This will let the finite safe-pair argument transfer complete-good
congruence orbits through the same original R_c raw structure.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {V : Type t}
variable {d : RawDatum G C}

/-- Every genuine cross-E effective colour of the raw fibre cover
is EXACTLY the original base effective colour, not just in its
congruence orbit. The baseline b is allowed to be arbitrary as
long as its reversal law makes the cover a raw presentation. -/
theorem rawCover_effectiveReduct_crossF
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = code.shift (D.F x y) - b x y)
    (X Y : RawCoverVertex V L)
    (hxy : ¬D.part X.1 Y.1) :
    (rawCoverPresentation D code b hb).effectiveReduct.F X Y =
      D.F X.1 Y.1 := by
  classical
  let c : C :=
    (code.decode (D.F X.1 Y.1)
      (rawResidual (X.2 Y.1) (Y.2 X.1) (b X.1 Y.1))).val
  have hc :
      (rawCoverPresentation D code b hb).colour X Y = some c := by
    change rawCoverColour D code b X Y = some c
    simp only [rawCoverColour, if_neg hxy]
  calc
    (rawCoverPresentation D code b hb).effectiveReduct.F X Y =
        d.phi c :=
      ((rawCoverPresentation D code b hb).effectiveReduct_crossColour
        X Y c hc).symm
    _ = D.F X.1 Y.1 :=
      rawCoverColour_phi D code b X Y hxy c hc

end SemigenericEPPA
