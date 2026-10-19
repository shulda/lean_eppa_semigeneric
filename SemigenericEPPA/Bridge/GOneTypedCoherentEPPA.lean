import SemigenericEPPA.Valuations.GOneGlobalCoherentRawFunctor
import SemigenericEPPA.Bridge.RawExactFunctorToTypedCoherent

/-!
# Coherent EPPA in the original typed rectangle language when G=1

For every finite original raw rectangle presentation P with trivial
effective group G, choose ONE finite factorial-padded effective
witness and ONE universal finite residual raw cover, with the old
raw vertices embedded in the exact zero section.

The certified ordinary raw EPPA theorem extends all individual
old partial maps on that very witness. The certified safe-action
theorem gives true homomorphic raw-cover automorphism extensions
of the full automorphism group of EVERY induced substructure.

The finite exact groupoid construction chooses a reference old
substructure per old-isomorphism component, uses one group lift of
its stabilizer, extends all exact old connector isomorphisms, and
applies the conjugation formula. The resulting single global raw
automorphism functor preserves identity and exact composition,
literal E and EVERY ordered raw predicate P_c, and extends the
original old maps on their exact domains.

The upstream API bridge then converts the exact functor into an
actual typed CoherentExtension, respecting PartialEquiv.EqOnSource
and exactly matching CoherentTriple, with trivial language-action
component. The witness is finite and the choice of witness,
embedding, universal code and raw baseline PRECEDES all partial
maps, group actions and component choices.

This is the positive coherent EPPA theorem for the G=1 sector.
It does not imply the full coherent/noncoherent classification for
nontrivial G, the DLF criterion or finite SAP.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- A finite original G=1 raw rectangle presentation has one
finite witness with a bona fide typed coherent EPPA extension
in the original R1--R3 binary language. -/
theorem finite_typedCoherentEPPA_witness
    (P : RawRectanglePresentation d A) :
    Finite (GOneJointRawCarrier P) ∧
    ∃ (Q : RawRectanglePresentation d (GOneJointRawCarrier P))
      (psiTyped : Structure.Embedding
        (rectangleTrivialAction C) P.toStructure Q.toStructure),
      Structure.IsCoherentEPPAWitness
        (rectangleTrivialAction C) psiTyped := by
  classical
  have hFinite : Finite (GOneJointRawCarrier P) := by
    letI : Finite (GOneFactorialCarrier P) := inferInstance
    letI : Finite (UniversalResidualCarrier C) :=
      finite_universalResidualCarrier
    exact finite_rawCoverVertices
  obtain ⟨j, K, hInj, hPart, hPartial, hGroups⟩ :=
    RawRectanglePresentation.exists_gOneJointRawEPPA_andAllGroupLifts.
      {u, v, w, w} P
  let Q : RawRectanglePresentation d (GOneJointRawCarrier P) :=
    P.gOneJointRawPresentation j K
  let psi : A → GOneJointRawCarrier P :=
    P.gOneJointRawOldMap j
  let Aut := P.gOneJointRawAutGroup j K
  have hPsiInj : Function.Injective psi := by
    intro x y h
    exact hInj (congrArg Prod.fst h)
  have hPsiPart (x y : A) :
      Q.part (psi x) (psi y) ↔ P.part x y := by
    change P.gOneFactorialGeometry.part
      (P.gOneFactorialOldMap j x)
      (P.gOneFactorialOldMap j y) ↔ P.part x y
    exact hPart x y
  have hPsiColour (x y : A) :
      Q.colour (psi x) (psi y) = P.colour x y := by
    change rawCoverColour P.gOneFactorialGeometry
      K.code K.baseline
      (P.gOneFactorialOldMap j x,
        fun _ : GOneFactorialCarrier P =>
          (0 : UniversalResidualCarrier C))
      (P.gOneFactorialOldMap j y,
        fun _ : GOneFactorialCarrier P =>
          (0 : UniversalResidualCarrier C)) = P.colour x y
    exact K.old_colour x y
  have hConnector :
      ∀ (S T : Set A) (f : ExactPartialIso P S T),
        ∃ beta : Aut,
          ∀ x : S,
            beta.val (psi x.val) = psi (f.toEquiv x).val := by
    intro S T f
    exact P.exists_gOneExactRawArrowExtension
      j K hPartial S T f
  have hGroup :
      ∀ (S : Set A),
        ∃ rho : ExactPartialIso P S S →* Aut,
          ∀ (h : ExactPartialIso P S S) (x : S),
            (rho h).val (psi x.val) = psi (h.toEquiv x).val := by
    intro S
    let H := ExactPartialIso P S S
    let rho : H →* Equiv.Perm S :=
      ExactPartialIso.autAction P S
    have hE : ∀ (h : H) (x y : S),
        P.part x.val y.val ↔
          P.part (rho h x).val (rho h y).val :=
      ExactPartialIso.autAction_part P S
    have hRaw : ∀ (h : H) (x y : S),
        P.colour (rho h x).val (rho h y).val =
          P.colour x.val y.val :=
      ExactPartialIso.autAction_colour P S
    exact P.exists_gOneRawSubgroupLift
      j K hGroups H S rho hE hRaw
  obtain ⟨Phi, hid, hcomp, hold⟩ :=
    P.exists_coherentRawLifts_onEveryComponent Aut psi
      hGroup hConnector
  let F : (S T : Set A) → ExactPartialIso P S T → Aut :=
    fun S T f => P.flattenCoherentRawComponents Aut Phi S T f
  have hFcomp : ∀ (S T U : Set A)
      (f : ExactPartialIso P S T) (g : ExactPartialIso P T U),
      F S U (g.comp f) = F T U g * F S T f := by
    intro S T U f g
    exact P.flattenCoherentRawComponents_comp
      Aut Phi hcomp S T U f g
  have hFext : ∀ (S T : Set A) (f : ExactPartialIso P S T) (x : S),
      (F S T f).val (psi x.val) = psi (f.toEquiv x).val := by
    intro S T f x
    exact P.flattenCoherentRawComponents_old
      Aut psi Phi hold S T f x
  obtain ⟨psiTyped, hCoherent⟩ :=
    P.coherentTypedEPPA_of_exactRawFunctor
      Q psi hPsiInj hPsiPart hPsiColour F hFcomp hFext
  exact ⟨hFinite, Q, psiTyped, hCoherent⟩

end RawRectanglePresentation

end SemigenericEPPA
