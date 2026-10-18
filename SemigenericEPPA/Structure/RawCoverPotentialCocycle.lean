import SemigenericEPPA.Structure.RawCoverAutomorphisms
import Mathlib.Tactic.Abel

/-!
# Potential corrections and composition of raw-cover transports

For one chosen family of additive potentials nu_X(Y) and a base
permutation theta, put

    d^theta_(X,Y) = nu_(theta X)(theta Y) - nu_X(Y).

The identity (4.10) in the manuscript is the telescoping cocycle

    d^(k theta)_(X,Y) =
        d^theta_(X,Y) + d^k_(theta X,theta Y).

We prove this directly and establish that the resulting actual
raw-cover vertex equivalences compose, with NO assumption that G
is commutative or that the raw fibres have a fixed reversal colour.

This is the algebraic homomorphism gate for the fixed-cover
finite-group raw lift. It is independent from the separate geometric
requirement that the potentials come from an invariant raw
colouring; the latter guarantees each lifted permutation preserves
the raw predicates.
-/

namespace SemigenericEPPA

universe u v
variable {V : Type u} {L : Type v} [AddCommGroup L]

/-- The manuscript's potential difference (4.9), evaluated on
one ordered base pair. -/
def rawPotentialCorrection
    (nu : V → V → L) (theta : Equiv.Perm V)
    (x y : V) : L :=
  nu (theta x) (theta y) - nu x y

/-- Exact cocycle equation (4.10), with composition ordered as
first theta, then kappa, and NO torsion or finiteness assumptions. -/
theorem rawPotentialCorrection_trans
    (nu : V → V → L) (theta kappa : Equiv.Perm V)
    (x y : V) :
    rawPotentialCorrection nu (theta.trans kappa) x y =
      rawPotentialCorrection nu theta x y +
        rawPotentialCorrection nu kappa (theta x) (theta y) := by
  unfold rawPotentialCorrection
  change nu (kappa (theta x)) (kappa (theta y)) - nu x y =
    (nu (theta x) (theta y) - nu x y) +
      (nu (kappa (theta x)) (kappa (theta y)) -
        nu (theta x) (theta y))
  abel

/-- Raw-cover transports compose with the pointwise semidirect
correction law d + theta.pullback(e). Both sides are genuine
equivalences of the FULL residual vertex carrier. -/
theorem rawCoverTransport_trans
    (theta kappa : Equiv.Perm V)
    (d e : V → V → L) :
    (rawCoverTransport theta d).trans (rawCoverTransport kappa e) =
      rawCoverTransport (theta.trans kappa)
        (fun x y => d x y + e (theta x) (theta y)) := by
  apply Equiv.ext
  intro X
  apply Prod.ext
  · rfl
  · funext z
    obtain ⟨y, rfl⟩ := (theta.trans kappa).surjective z
    have h1 := rawCoverTransport_coord theta d X y
    have h2 := rawCoverTransport_coord kappa e
      (rawCoverTransport theta d X) (theta y)
    have h3 := rawCoverTransport_coord
      (theta.trans kappa)
      (fun x y => d x y + e (theta x) (theta y)) X y
    calc
      (((rawCoverTransport theta d).trans
          (rawCoverTransport kappa e)) X).2
          ((theta.trans kappa) y) =
        ((rawCoverTransport theta d) X).2 (theta y) +
          e (theta X.1) (theta y) := by
            change ((rawCoverTransport kappa e)
              ((rawCoverTransport theta d) X)).2 (kappa (theta y)) =
                ((rawCoverTransport theta d) X).2 (theta y) +
                  e (theta X.1) (theta y)
            exact h2
      _ = (X.2 y + d X.1 y) +
          e (theta X.1) (theta y) := by rw [h1]
      _ = X.2 y + (d X.1 y + e (theta X.1) (theta y)) := by
            abel
      _ = (rawCoverTransport (theta.trans kappa)
            (fun x y => d x y + e (theta x) (theta y)) X).2
            ((theta.trans kappa) y) := h3.symm

/-- The vertex permutation induced by a fixed array of potentials. -/
def rawCoverPotentialLift
    (nu : V → V → L) (theta : Equiv.Perm V) :
    RawCoverVertex V L ≃ RawCoverVertex V L :=
  rawCoverTransport theta (rawPotentialCorrection nu theta)

/-- Potential-based raw lifts compose exactly (not merely up to
a gauge or on a substructure), the key algebra needed for
homomorphic finite-group raw lifts. -/
theorem rawCoverPotentialLift_trans
    (nu : V → V → L) (theta kappa : Equiv.Perm V) :
    (rawCoverPotentialLift nu theta).trans
        (rawCoverPotentialLift nu kappa) =
      rawCoverPotentialLift nu (theta.trans kappa) := by
  change (rawCoverTransport theta (rawPotentialCorrection nu theta)).trans
      (rawCoverTransport kappa (rawPotentialCorrection nu kappa)) =
      rawCoverTransport (theta.trans kappa)
        (rawPotentialCorrection nu (theta.trans kappa))
  rw [rawCoverTransport_trans]
  have hcorr :
      (fun x y =>
        rawPotentialCorrection nu theta x y +
          rawPotentialCorrection nu kappa (theta x) (theta y)) =
        rawPotentialCorrection nu (theta.trans kappa) := by
    funext x y
    exact (rawPotentialCorrection_trans nu theta kappa x y).symm
  rw [hcorr]

/-- The potential transport corresponding to the identity base
permutation is the literal identity permutation of the cover. -/
theorem rawCoverPotentialLift_id
    (nu : V → V → L) :
    rawCoverPotentialLift nu (Equiv.refl V) =
      Equiv.refl (RawCoverVertex V L) := by
  apply Equiv.ext
  intro X
  apply Prod.ext
  · rfl
  · funext y
    change X.2 y + (nu X.1 y - nu X.1 y) = X.2 y
    abel

end SemigenericEPPA
