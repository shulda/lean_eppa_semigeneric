import SemigenericEPPA.Bridge.ExactRawAutomorphismGroups
import Mathlib.Tactic.Group

/-!
# Exact raw groupoid arrows as a stabilizer with connectors

Fix one reference induced raw substructure R, a family of induced old
substructures F(i) isomorphic to R, and choose an EXACT old connector
  gamma_i : R ≃ F(i)
preserving the original E-relation and ALL raw colours.

Any raw isomorphism f : F(i) ≃ F(j) has a canonical coordinate
  gamma_j^{-1} ◦ f ◦ gamma_i ∈ Aut(P|R).
The coordinate preserves identities and compositions ON THE NOSE.

Given one homomorphic lift of Aut(P|R) to Perm(W), and arbitrary
whole-witness automorphisms beta_i extending connectors gamma_i,
the conjugation formula
  Phi(i,j,f) = beta_j * lift(gamma_j^{-1} f gamma_i) * beta_i^{-1}
provides exact identities and composition. Nothing is assumed
about the coherence of the beta_i choices.

This is a fully typed one-component groupoid FUNCTOR statement,
not yet the global selection of components or connector lifts.
-/

namespace SemigenericEPPA

universe u v w t q

variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w}
variable {d : RawDatum G C}
variable {I : Type t} {W : Type q}

namespace RawRectanglePresentation.ExactPartialIso

/-- The canonical reference-coordinate automorphism of a fixed
induced raw reference R representing one groupoid component. -/
def referenceCoordinate
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (i j : I)
    (f : ExactPartialIso P (F i) (F j)) :
    ExactPartialIso P R R :=
  (gamma j).symm.comp (f.comp (gamma i))

/-- The identity arrow on F(i) has the identity reference coordinate. -/
theorem referenceCoordinate_id
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (i : I) :
    referenceCoordinate P R F gamma i i (refl P (F i)) = 1 := by
  apply ext
  apply Equiv.ext
  intro x
  change (gamma i).toEquiv.symm ((gamma i).toEquiv x) = x
  exact (gamma i).toEquiv.symm_apply_apply x

/-- Source/target compatible exact raw-arrow composition becomes
the group multiplication in Aut(P|R), with the correct order. -/
theorem referenceCoordinate_comp
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (i j k : I)
    (f : ExactPartialIso P (F i) (F j))
    (g : ExactPartialIso P (F j) (F k)) :
    referenceCoordinate P R F gamma i k (g.comp f) =
      referenceCoordinate P R F gamma j k g *
        referenceCoordinate P R F gamma i j f := by
  apply ext
  apply Equiv.ext
  intro x
  change (gamma k).toEquiv.symm
      (g.toEquiv (f.toEquiv ((gamma i).toEquiv x))) =
    (gamma k).toEquiv.symm
      (g.toEquiv ((gamma j).toEquiv
        ((gamma j).toEquiv.symm
          (f.toEquiv ((gamma i).toEquiv x)))))
  rw [(gamma j).toEquiv.apply_symm_apply]

/-- An actual strict coherent extension on ONE groupoid component,
provided a homomorphic automorphism lift of its reference object
and arbitrary full-witness connector permutations are given. -/
def referenceCoherentArrow
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (rho : ExactPartialIso P R R →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (i j : I) (f : ExactPartialIso P (F i) (F j)) :
    Equiv.Perm W :=
  beta j * rho (referenceCoordinate P R F gamma i j f) *
    (beta i)⁻¹

/-- Strict functorial identity, independent of connector choices. -/
theorem referenceCoherentArrow_id
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (rho : ExactPartialIso P R R →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (i : I) :
    referenceCoherentArrow P R F gamma rho beta
      i i (refl P (F i)) = 1 := by
  simp [referenceCoherentArrow, referenceCoordinate_id]

/-- Strict functorial composition on every composable pair of raw
partial isomorphisms in this one connected component. -/
theorem referenceCoherentArrow_comp
    (P : RawRectanglePresentation d A)
    (R : Set A) (F : I → Set A)
    (gamma : ∀ i : I, ExactPartialIso P R (F i))
    (rho : ExactPartialIso P R R →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (i j k : I)
    (f : ExactPartialIso P (F i) (F j))
    (g : ExactPartialIso P (F j) (F k)) :
    referenceCoherentArrow P R F gamma rho beta
      i k (g.comp f) =
        referenceCoherentArrow P R F gamma rho beta j k g *
          referenceCoherentArrow P R F gamma rho beta i j f := by
  simp only [referenceCoherentArrow, referenceCoordinate_comp, map_mul]
  group

end RawRectanglePresentation.ExactPartialIso

end SemigenericEPPA
