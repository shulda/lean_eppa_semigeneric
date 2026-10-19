import SemigenericEPPA.Bridge.CoherentRawComponentAutArrow

/-!
# Choose coherent raw lifts in EVERY isomorphism component simultaneously

A standard finite-groupoid principle underlies the G=1 coherent
EPPA construction:

1. For every induced old substructure R, its FULL automorphism
   group Aut(P|R) admits one genuine homomorphic lift to the true
   whole-witness automorphism group K.
2. For every exact old raw isomorphism f:S→T, some genuine member
   beta∈K extends f along one fixed old embedding psi:A→W.

From these two data, all connected components of the exact old
raw groupoid admit simultaneous coherent extension functors.
Choose one representative R_q per isomorphism component q, one
homomorphic stabilizer lift rho_q, and a whole-witness extension
beta_{q,i} of every chosen raw connector gamma_{q,i}:R_q→S_i.
All choices are made ONCE before selecting any arrow f.

The formula beta_{q,j} rho_q(gamma_j^-1 f gamma_i) beta_{q,i}^-1
then gives a strict identity/composition/old-vertex-extension
functor with values in the genuine subgroup K, component by
component. Nothing is assumed about individual connector
coherence.

This theorem does not yet erase the component indexing of arrows
or convert to the upstream typed CoherentExtension. Those are
the final indexing and API gates.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {A : Type w} {W : Type t}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The exact two general extension properties needed to perform
a global coherent groupoid assembly, with no separate witness or
permutation group chosen after the component. -/
theorem exists_coherentRawLifts_onEveryComponent
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (psi : A → W)
    (hGroups : ∀ (S : Set A),
      ∃ rho : ExactPartialIso P S S →* K,
        ∀ (h : ExactPartialIso P S S) (x : S),
          (rho h).val (psi x.val) = psi (h.toEquiv x).val)
    (hConnector : ∀ (S T : Set A)
        (f : ExactPartialIso P S T),
      ∃ beta : K,
        ∀ x : S,
          beta.val (psi x.val) = psi (f.toEquiv x).val) :
    ∃ Phi : (q : RawIsoComponent P) →
          (i j : RawComponentObject P q) →
            ExactPartialIso P i.val j.val → K,
      (∀ (q : RawIsoComponent P)
        (i : RawComponentObject P q),
        Phi q i i (ExactPartialIso.refl P i.val) = 1) ∧
      (∀ (q : RawIsoComponent P)
        (i j k : RawComponentObject P q)
        (f : ExactPartialIso P i.val j.val)
        (g : ExactPartialIso P j.val k.val),
        Phi q i k (g.comp f) =
          Phi q j k g * Phi q i j f) ∧
      (∀ (q : RawIsoComponent P)
        (i j : RawComponentObject P q)
        (f : ExactPartialIso P i.val j.val) (x : i.val),
        (Phi q i j f).val (psi x.val) = psi (f.toEquiv x).val) := by
  classical
  let hg (q : RawIsoComponent P) :=
    hGroups (P.rawIsoRepresentative q)
  let rho (q : RawIsoComponent P) :
      ExactPartialIso P (P.rawIsoRepresentative q)
        (P.rawIsoRepresentative q) →* K :=
    Classical.choose (hg q)
  have hrho (q : RawIsoComponent P)
      (h : ExactPartialIso P (P.rawIsoRepresentative q)
        (P.rawIsoRepresentative q))
      (x : P.rawIsoRepresentative q) :
      (rho q h).val (psi x.val) = psi (h.toEquiv x).val :=
    (Classical.choose_spec (hg q)) h x
  let hc (q : RawIsoComponent P)
      (i : RawComponentObject P q) :=
    hConnector (P.rawIsoRepresentative q) i.val
      (P.componentRawConnectors q i)
  let beta (q : RawIsoComponent P)
      (i : RawComponentObject P q) : K :=
    Classical.choose (hc q i)
  have hbeta (q : RawIsoComponent P)
      (i : RawComponentObject P q)
      (x : P.rawIsoRepresentative q) :
      (beta q i).val (psi x.val) =
        psi ((P.componentRawConnectors q i).toEquiv x).val :=
    (Classical.choose_spec (hc q i)) x
  let Phi (q : RawIsoComponent P)
      (i j : RawComponentObject P q)
      (f : ExactPartialIso P i.val j.val) : K :=
    P.coherentComponentAutArrow q K (rho q) (beta q) i j f
  refine ⟨Phi, ?_, ?_, ?_⟩
  · intro q i
    exact P.coherentComponentAutArrow_id q K (rho q) (beta q) i
  · intro q i j k f g
    exact P.coherentComponentAutArrow_comp q K
      (rho q) (beta q) i j k f g
  · intro q i j f x
    exact P.coherentComponentAutArrow_old q K
      (rho q) (beta q) psi
      (hrho q) (hbeta q) i j f x

end RawRectanglePresentation

end SemigenericEPPA
