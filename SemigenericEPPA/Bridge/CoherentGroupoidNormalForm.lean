import SemigenericEPPA.Bridge.CoherentEPPA
import Mathlib.Tactic.Group

/-!
# The coherent groupoid normal form from automorphism group lifts

A genuine coherent extension is not merely an unrelated H-action on
each induced substructure. Fix a representative object U in one
connected component of the exact partial-isomorphism groupoid.
Let rho:Perm(U)→*Perm(W) be ONE homomorphic lift of its automorphism
group. For every other object i in the component, fix a connector
beta_i ∈ Perm(W) extending a chosen isomorphism from U to i.

For a representative-coordinate isomorphism f:U≃U from i to j,
define
  Phi(i,j,f) = beta_j * rho(f) * beta_i^-1.

This source of coherence proves the exact identity and composition
laws simultaneously; the old-vertex extension equation is inherited
from rho and the chosen connectors. In particular, NO functoriality
of the independently chosen connectors is assumed.

This is the generic algebraic core of the manuscript's C0 gate.
A later theorem must instantiate representatives, domains, connector
isomorphisms and upstream PartialIsomorphism.CoherentTriple.
-/

namespace SemigenericEPPA

universe u v w
variable {I : Type u} {U : Type v} {W : Type w}

/-- A fixed model automorphism-group lift transported across
arbitrary chosen object connectors. -/
noncomputable def coherentGroupoidNormalForm
    (rho : Equiv.Perm U →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (i j : I)
    (f : Equiv.Perm U) : Equiv.Perm W :=
  beta j * rho f * (beta i)⁻¹

/-- All identity arrows are mapped to the identity permutation,
regardless of how the object connectors were chosen. -/
theorem coherentGroupoidNormalForm_id
    (rho : Equiv.Perm U →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (i : I) :
    coherentGroupoidNormalForm rho beta i i 1 = 1 := by
  simp [coherentGroupoidNormalForm]

/-- Exact categorical composition: first f from i to j, then g
from j to k. No finite type or commutativity hypotheses are used. -/
theorem coherentGroupoidNormalForm_comp
    (rho : Equiv.Perm U →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (i j k : I)
    (f g : Equiv.Perm U) :
    coherentGroupoidNormalForm rho beta i k (g * f) =
      coherentGroupoidNormalForm rho beta j k g *
        coherentGroupoidNormalForm rho beta i j f := by
  simp only [coherentGroupoidNormalForm, map_mul]
  group

/-- The old copy at component object i is beta_i applied to the
distinguished model copy. -/
def coherentGroupoidOldMap
    (psi : U → W)
    (beta : I → Equiv.Perm W)
    (i : I) (x : U) : W :=
  beta i (psi x)

/-- Every transported representative-coordinate arrow acts exactly
as prescribed on the embedded old vertices. -/
theorem coherentGroupoidNormalForm_old
    (rho : Equiv.Perm U →* Equiv.Perm W)
    (beta : I → Equiv.Perm W)
    (psi : U → W)
    (hRho : ∀ (f : Equiv.Perm U) (x : U),
      rho f (psi x) = psi (f x))
    (i j : I) (f : Equiv.Perm U) (x : U) :
    coherentGroupoidNormalForm rho beta i j f
        (coherentGroupoidOldMap psi beta i x) =
      coherentGroupoidOldMap psi beta j (f x) := by
  change beta j (rho f ((beta i).symm (beta i (psi x)))) =
      beta j (psi (f x))
  rw [(beta i).symm_apply_apply, hRho f x]

end SemigenericEPPA
