import SemigenericEPPA.Bridge.ExactRawGroupoidCoherentTransport

/-!
# Exact old-vertex extension for the reference groupoid functor

The same one-component groupoid normal form has already been proved
to preserve identity and composition. Here we verify its genuinely
mathematical extension property: if the chosen whole-witness beta_i
permutes the literal old vertices exactly as the selected raw
connector gamma_i, and one homomorphism rho lifts the actual raw
automorphism group of the reference R, the formula
   beta_j * rho(gamma_j^{-1} f gamma_i) * beta_i^{-1}
extends EVERY exact old isomorphism f:F(i)→F(j).

All equalities refer to the SAME preselected old embedding psi and
the SAME underlying witness W. No choice or finiteness conditions,
and no assumption of coherent beta_i connectors, are used.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w}
variable {d : RawDatum G C}
variable {I : Type t} {W : Type q}

namespace RawRectanglePresentation.ExactPartialIso

/-- The coherent one-component permutation extends EVERY raw old
groupoid arrow on the literal old embedded vertices. -/
theorem referenceCoherentArrow_old
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (rho : ExactPartialIso P R R →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (psi : A → W)
    (hRho : ∀ (h : ExactPartialIso P R R) (x : R),
      rho h (psi x.val) = psi (h.toEquiv x).val)
    (hBeta : ∀ (i : I) (x : R),
      beta i (psi x.val) = psi ((gamma i).toEquiv x).val)
    (i j : I) (f : ExactPartialIso P (F i) (F j))
    (x : F i) :
    referenceCoherentArrow P R F gamma rho beta i j f (psi x.val) =
      psi (f.toEquiv x).val := by
  let r : R := (gamma i).toEquiv.symm x
  have hr : (gamma i).toEquiv r = x :=
    (gamma i).toEquiv.apply_symm_apply x
  have hConnectI : beta i (psi r.val) = psi x.val := by
    simpa only [hr] using hBeta i r
  have hCoordinate :
      (referenceCoordinate P R F gamma i j f).toEquiv r =
        (gamma j).toEquiv.symm (f.toEquiv x) := by
    change (gamma j).toEquiv.symm
      (f.toEquiv ((gamma i).toEquiv r)) =
        (gamma j).toEquiv.symm (f.toEquiv x)
    rw [hr]
  have hConnectJ :
      beta j (psi ((gamma j).toEquiv.symm (f.toEquiv x)).val) =
        psi (f.toEquiv x).val := by
    simpa only [(gamma j).toEquiv.apply_symm_apply] using
      hBeta j ((gamma j).toEquiv.symm (f.toEquiv x))
  change beta j
      (rho (referenceCoordinate P R F gamma i j f)
        ((beta i).symm (psi x.val))) =
    psi (f.toEquiv x).val
  calc
    beta j
        (rho (referenceCoordinate P R F gamma i j f)
          ((beta i).symm (psi x.val))) =
      beta j
        (rho (referenceCoordinate P R F gamma i j f)
          (psi r.val)) := by
            rw [← hConnectI, (beta i).symm_apply_apply]
    _ = beta j
        (psi ((referenceCoordinate P R F gamma i j f).toEquiv r).val) :=
          congrArg (beta j)
            (hRho (referenceCoordinate P R F gamma i j f) r)
    _ = beta j
        (psi ((gamma j).toEquiv.symm (f.toEquiv x)).val) := by
          rw [hCoordinate]
    _ = psi (f.toEquiv x).val := hConnectJ

end RawRectanglePresentation.ExactPartialIso

end SemigenericEPPA
