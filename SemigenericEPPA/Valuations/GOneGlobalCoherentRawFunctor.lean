import SemigenericEPPA.Valuations.GOneCoherentAllComponents
import SemigenericEPPA.Bridge.FlattenCoherentRawGroupoid

/-!
# One global strictly coherent exact raw groupoid functor for G=1

For any finite original literal raw rectangle presentation P with
trivial effective group G, a single factorial-padded effective base
and one finite universal raw residual cover are chosen BEFORE
selecting any old partial isomorphism, induced subgroup or
groupoid component.

The fixed witness has ordinary raw EPPA and true homomorphic
automorphism group extensions on every induced substructure.
The component construction selects once and for all a reference
old substructure for every raw-isomorphism class and a whole-
witness extension of every old connector, and builds a strict
coherent functor on each groupoid component.

The flattening theorem then gives ONE coherent global map F
defined for EVERY exact induced raw partial-isomorphism arrow
f:S≃T, valued in the GENUINE raw automorphism subgroup of the
SAME finite witness. This map preserves identity and strict
composition and extends every old map on the fixed zero-section
embedding, with no source-domain shrinking and no change of
raw colours.

The only remaining conversion is to the existing upstream
AllThoseEPPA IsCoherentEPPAWitness typed API, whose exact
Equivalent/CoherentTriple compatibility is formalized separately.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- One fixed finite raw witness supports a truly GLOBAL coherent
assignment of all exact induced old raw arrows, taking values
in the literal raw automorphism group of the SAME witness. -/
theorem exists_gOneGlobalCoherentExactRawFunctor
    (P : RawRectanglePresentation d A) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (K : FixedJointRawCover.{u, v, w, w, w}
        P P.gOneFactorialGeometry (P.gOneFactorialOldMap j))
      (F : (S T : Set A) → ExactPartialIso P S T →
        P.gOneJointRawAutGroup j K),
      (∀ (S : Set A),
        F S S (ExactPartialIso.refl P S) = 1) ∧
      (∀ (S T U : Set A)
        (f : ExactPartialIso P S T)
        (g : ExactPartialIso P T U),
        F S U (g.comp f) = F T U g * F S T f) ∧
      (∀ (S T : Set A) (f : ExactPartialIso P S T) (x : S),
        (F S T f).val (P.gOneJointRawOldMap j x.val) =
          P.gOneJointRawOldMap j (f.toEquiv x).val) := by
  classical
  obtain ⟨j, K, Phi, hId, hComp, hOld⟩ :=
    P.exists_gOneCoherentRawLifts_onAllComponents
  let Aut := P.gOneJointRawAutGroup j K
  let F : (S T : Set A) → ExactPartialIso P S T → Aut :=
    fun S T f => P.flattenCoherentRawComponents Aut Phi S T f
  refine ⟨j, K, F, ?_, ?_, ?_⟩
  · intro S
    exact P.flattenCoherentRawComponents_id Aut Phi hId S
  · intro S T U f g
    exact P.flattenCoherentRawComponents_comp Aut Phi
      hComp S T U f g
  · intro S T f x
    exact P.flattenCoherentRawComponents_old Aut
      (P.gOneJointRawOldMap j) Phi hOld S T f x

end RawRectanglePresentation

end SemigenericEPPA
