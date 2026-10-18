import SemigenericEPPA.Algebra.PrescribedRawCorrections

/-!
# Raw-label preservation implies compatibility of prescribed corrections

The crucial compatibility check in part (iv) of the raw-fibre cover
lemma is not an independent algebraic assumption. For an old-domain
pair x,y, suppose the original residual label equals the target
residual label after the desired partial map:

  eta'_x(theta y) - eta'_y(theta x) + b(theta x,theta y)
    = eta_x(y) - eta_y(x) + b(x,y).

The prescribed row correction is, by (3.28),

  R(x,y) = eta'_x(theta y) - eta_x(y).

Subtracting the reversed prescription gives exactly (3.24).
We prove this identity and combine it with the finite
prescribed-row extension theorem to construct global corrections
satisfying both old-point extension and raw-edge preservation.

The next semantic gate will obtain the residual-label equality
from preservation of raw colours together with the SECTION-based
old embedding (3.26)--(3.27). The decoder need not be injective:
the fixed section makes the old residual value canonical.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]
variable {L : Type v} [AddCommGroup L]
variable {V : Type w}
variable {s : AffineAntiInvolution G}

/-- The precise correction row prescribed by a source residual
valuation and the desired target residual valuation under theta. -/
def oldRawCorrectionRow
    (theta : Equiv.Perm V)
    (etaSource etaTarget : V → V → L)
    (x y : V) : L :=
  etaTarget x (theta y) - etaSource x y

/-- Equality of the full old and target residual labels on a pair
forces equation (3.24) between its two prescribed correction rows. -/
theorem oldRawCorrectionRow_compatible
    (theta : Equiv.Perm V)
    (b : V → V → L)
    (etaSource etaTarget : V → V → L)
    (x y : V)
    (hlabel :
      rawResidual (etaTarget x (theta y))
          (etaTarget y (theta x)) (b (theta x) (theta y)) =
        rawResidual (etaSource x y) (etaSource y x) (b x y)) :
    oldRawCorrectionRow theta etaSource etaTarget x y -
      oldRawCorrectionRow theta etaSource etaTarget y x =
        b x y - b (theta x) (theta y) := by
  calc
    oldRawCorrectionRow theta etaSource etaTarget x y -
        oldRawCorrectionRow theta etaSource etaTarget y x =
      rawResidual (etaTarget x (theta y))
          (etaTarget y (theta x)) (b (theta x) (theta y)) -
        rawResidual (etaSource x y) (etaSource y x) (b x y) +
        (b x y - b (theta x) (theta y)) := by
          simp only [oldRawCorrectionRow, rawResidual]
          abel
    _ = b x y - b (theta x) (theta y) := by
      rw [hlabel]
      simp

/-- Every finite family of old source/target residual valuations
whose pairwise raw residual labels agree admits ONE global
correction extending all prescribed rows and satisfying (3.24).

Thus the actual raw-cover transport (3.25) can send each prescribed
old vertex to its specified target when the effective base theta
extends the old base map. The valuation equality uses every y,
including same-E dummy coordinates, not only cross-part targets. -/
theorem exists_oldRawCorrectionExtension
    [Finite V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (b : V → V → L)
    (hb : ∀ x y, ¬D.part x y →
      b y x = t (D.F x y) - b x y)
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
    ∃ correction : V → V → L,
      (∀ x y, x ∈ S →
        correction x y = etaTarget x (theta y) - etaSource x y) ∧
      (∀ x y, ¬D.part x y →
        correction x y - correction y x =
          b x y - b (theta x) (theta y)) := by
  let R : V → V → L :=
    oldRawCorrectionRow theta etaSource etaTarget
  have hR : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      R x y - R y x =
        b x y - b (theta x) (theta y) := by
    intro x y hx hy hxy
    exact oldRawCorrectionRow_compatible theta b
      etaSource etaTarget x y (hlabel x y hx hy hxy)
  obtain ⟨correction, hprescribed, hglobal⟩ :=
    exists_finitePrescribedResidualCorrections
      D t b hb theta hE hF S R hR
  exact ⟨correction, hprescribed, hglobal⟩

end SemigenericEPPA
