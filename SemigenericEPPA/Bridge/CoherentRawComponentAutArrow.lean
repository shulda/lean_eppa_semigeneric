import SemigenericEPPA.Bridge.ExactRawGroupoidOldExtension
import SemigenericEPPA.Bridge.ExactRawGroupoidComponents
import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup

/-!
# One coherent component with values in TRUE raw automorphisms

For each connected component q of the exact old raw groupoid,
the already certified raw-isomorphism setoid selects one
representative old induced substructure R_q and exact connectors
gamma_i : R_q ≃ S_i.

If rho:Aut(P|R_q)→*K is an honest homomorphism into some subgroup
K≤Perm(W) consisting of genuine whole-witness raw automorphisms,
and beta_i∈K are arbitrary connector extensions, define
  Phi_q(i,j,f) = beta_j rho(gamma_j^-1 f gamma_i) beta_i^-1.

Unlike the elementary permutation-valued normal form, this lands
in K ON THE NOSE. Identity, composition and old-vertex extension
are proved with exactly typed induced raw isomorphism arrows.

The underlying global choice of rho and beta for ALL q, and
the final upstream CoherentExtension bridge, remain separate.
-/

namespace SemigenericEPPA

universe u v w t z
variable {G : Type u} [Group G] {C : Type v}
variable {A : Type w} {W : Type z}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Canonical exact old-connector family on one groupoid component. -/
noncomputable def componentRawConnectors
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P) :
    ∀ i : RawComponentObject P q,
      ExactPartialIso P (P.rawIsoRepresentative q) i.val :=
  fun i => P.rawComponentConnector q i

/-- Strict coherent transport in a TRUE raw automorphism subgroup
for all exact old arrows in one isomorphism component. -/
noncomputable def coherentComponentAutArrow
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P)
    (K : Subgroup (Equiv.Perm W))
    (rho : ExactPartialIso P (P.rawIsoRepresentative q)
      (P.rawIsoRepresentative q) →* K)
    (beta : RawComponentObject P q → K)
    (i j : RawComponentObject P q)
    (f : ExactPartialIso P i.val j.val) : K :=
  beta j *
    rho (ExactPartialIso.referenceCoordinate
      P (P.rawIsoRepresentative q)
      (P.rawComponentObjects q)
      (P.componentRawConnectors q) i j f) *
    (beta i)⁻¹

/-- Every identity arrow is sent to the identity RAW
automorphism, independently of all connector choices. -/
theorem coherentComponentAutArrow_id
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P)
    (K : Subgroup (Equiv.Perm W))
    (rho : ExactPartialIso P (P.rawIsoRepresentative q)
      (P.rawIsoRepresentative q) →* K)
    (beta : RawComponentObject P q → K)
    (i : RawComponentObject P q) :
    P.coherentComponentAutArrow q K rho beta i i
      (ExactPartialIso.refl P i.val) = 1 := by
  change beta i *
      rho (ExactPartialIso.referenceCoordinate P
        (P.rawIsoRepresentative q) (P.rawComponentObjects q)
        (P.componentRawConnectors q) i i
        (ExactPartialIso.refl P i.val)) * (beta i)⁻¹ = 1
  have hcoord :
      ExactPartialIso.referenceCoordinate P
        (P.rawIsoRepresentative q) (P.rawComponentObjects q)
        (P.componentRawConnectors q) i i
          (ExactPartialIso.refl P i.val) = 1 :=
    ExactPartialIso.referenceCoordinate_id P
      (P.rawIsoRepresentative q) (P.rawComponentObjects q)
      (P.componentRawConnectors q) i
  rw [hcoord, map_one]
  group

/-- Exact groupoid composition into the true raw-automorphism
subgroup, with no supplementary coherence of beta. -/
theorem coherentComponentAutArrow_comp
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P)
    (K : Subgroup (Equiv.Perm W))
    (rho : ExactPartialIso P (P.rawIsoRepresentative q)
      (P.rawIsoRepresentative q) →* K)
    (beta : RawComponentObject P q → K)
    (i j k : RawComponentObject P q)
    (f : ExactPartialIso P i.val j.val)
    (g : ExactPartialIso P j.val k.val) :
    P.coherentComponentAutArrow q K rho beta i k (g.comp f) =
      P.coherentComponentAutArrow q K rho beta j k g *
        P.coherentComponentAutArrow q K rho beta i j f := by
  change beta k *
        rho (ExactPartialIso.referenceCoordinate P
          (P.rawIsoRepresentative q) (P.rawComponentObjects q)
          (P.componentRawConnectors q) i k (g.comp f)) *
        (beta i)⁻¹ =
      (beta k * rho (ExactPartialIso.referenceCoordinate P
          (P.rawIsoRepresentative q) (P.rawComponentObjects q)
          (P.componentRawConnectors q) j k g) * (beta j)⁻¹) *
      (beta j * rho (ExactPartialIso.referenceCoordinate P
          (P.rawIsoRepresentative q) (P.rawComponentObjects q)
          (P.componentRawConnectors q) i j f) * (beta i)⁻¹)
  have hcoord :
      ExactPartialIso.referenceCoordinate P
        (P.rawIsoRepresentative q) (P.rawComponentObjects q)
        (P.componentRawConnectors q) i k (g.comp f) =
      ExactPartialIso.referenceCoordinate P
        (P.rawIsoRepresentative q) (P.rawComponentObjects q)
        (P.componentRawConnectors q) j k g *
      ExactPartialIso.referenceCoordinate P
        (P.rawIsoRepresentative q) (P.rawComponentObjects q)
        (P.componentRawConnectors q) i j f :=
    ExactPartialIso.referenceCoordinate_comp P
      (P.rawIsoRepresentative q) (P.rawComponentObjects q)
      (P.componentRawConnectors q) i j k f g
  rw [hcoord, map_mul]
  group

/-- The groupoid automorphism carries the original embedded old
vertex precisely to the image under the exact old arrow. -/
theorem coherentComponentAutArrow_old
    (P : RawRectanglePresentation d A)
    (q : RawIsoComponent P)
    (K : Subgroup (Equiv.Perm W))
    (rho : ExactPartialIso P (P.rawIsoRepresentative q)
      (P.rawIsoRepresentative q) →* K)
    (beta : RawComponentObject P q → K)
    (psi : A → W)
    (hRho : ∀ (h : ExactPartialIso P
        (P.rawIsoRepresentative q) (P.rawIsoRepresentative q))
        (x : P.rawIsoRepresentative q),
      (rho h).val (psi x.val) = psi (h.toEquiv x).val)
    (hBeta : ∀ (i : RawComponentObject P q)
        (x : P.rawIsoRepresentative q),
      (beta i).val (psi x.val) =
        psi ((P.componentRawConnectors q i).toEquiv x).val)
    (i j : RawComponentObject P q)
    (f : ExactPartialIso P i.val j.val)
    (x : i.val) :
    (P.coherentComponentAutArrow q K rho beta i j f).val
        (psi x.val) = psi (f.toEquiv x).val := by
  let incl : K →* Equiv.Perm W := K.subtype
  let rho' : ExactPartialIso P (P.rawIsoRepresentative q)
      (P.rawIsoRepresentative q) →* Equiv.Perm W :=
    incl.comp rho
  let beta' : RawComponentObject P q → Equiv.Perm W :=
    fun i => (beta i).val
  have hrho' : ∀ (h : ExactPartialIso P
      (P.rawIsoRepresentative q) (P.rawIsoRepresentative q))
      (x : P.rawIsoRepresentative q),
      rho' h (psi x.val) = psi (h.toEquiv x).val :=
    hRho
  have hbeta' : ∀ (i : RawComponentObject P q)
      (x : P.rawIsoRepresentative q),
      beta' i (psi x.val) =
        psi ((P.componentRawConnectors q i).toEquiv x).val :=
    hBeta
  exact ExactPartialIso.referenceCoherentArrow_old
    P (P.rawIsoRepresentative q)
    (P.rawComponentObjects q)
    (P.componentRawConnectors q)
    rho' beta' psi hrho' hbeta' i j f x

end RawRectanglePresentation

end SemigenericEPPA
