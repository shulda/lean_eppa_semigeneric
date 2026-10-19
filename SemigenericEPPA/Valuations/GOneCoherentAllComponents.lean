import SemigenericEPPA.Valuations.GOneActualRawAutSubgroupLifts
import SemigenericEPPA.Bridge.CoherentAllRawComponents

/-!
# Unconditional coherent raw groupoid extensions on EVERY component for G=1

The positive coherent branch requires a single finite raw witness,
chosen BEFORE selecting a partial isomorphism or a stabilizer group.
Our certified G=1 witness supplies exactly that: one factorial
effective base, one finite universal raw residual cover, one baseline,
one literal original old zero-section embedding, ordinary EPPA, and
homomorphic raw-automorphism lifts of every old induced-substructure
group action.

The actual finite group of automorphisms Aut(P|R) of each induced
reference object acts on its old vertices; apply the homomorphic
raw-subgroup lift to that ACTION, and use ordinary raw EPPA to
extend each chosen exact old connector gamma_i:R→S_i.

The abstract all-component groupoid theorem then yields, for
EVERY component q simultaneously, a STRICT functor assigning a
genuine automorphism of the SAME fixed raw witness to each exact
old groupoid arrow within q, preserving identity, composition,
every literal raw predicate, and the old action on the nose.

The component indices are still part of the statement. The final
gate is to flatten those indices for arbitrary source/target sets
and translate to the upstream typed CoherentExtension with
Equivalent and CoherentTriple.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- One fixed finite raw cover and one literal old embedding support
strict coherent subgroup-valued extension functors for ALL
isomorphism components of exact induced raw partial maps. -/
theorem exists_gOneCoherentRawLifts_onAllComponents
    (P : RawRectanglePresentation d A) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (K : FixedJointRawCover.{u, v, w, w, max u (max v w)}
        P P.gOneFactorialGeometry (P.gOneFactorialOldMap j))
      (Phi : (q : RawIsoComponent P) →
        (i k : RawComponentObject P q) →
          ExactPartialIso P i.val k.val →
            P.gOneJointRawAutGroup j K),
      (∀ (q : RawIsoComponent P)
        (i : RawComponentObject P q),
        Phi q i i (ExactPartialIso.refl P i.val) = 1) ∧
      (∀ (q : RawIsoComponent P)
        (i k l : RawComponentObject P q)
        (f : ExactPartialIso P i.val k.val)
        (g : ExactPartialIso P k.val l.val),
        Phi q i l (g.comp f) =
          Phi q k l g * Phi q i k f) ∧
      (∀ (q : RawIsoComponent P)
        (i k : RawComponentObject P q)
        (f : ExactPartialIso P i.val k.val) (x : i.val),
        (Phi q i k f).val
          (P.gOneJointRawOldMap j x.val) =
            P.gOneJointRawOldMap j (f.toEquiv x).val) := by
  classical
  obtain ⟨j, K, _he, _hPart, hPartial, hGroups⟩ :=
    RawRectanglePresentation.exists_gOneJointRawEPPA_andAllGroupLifts.{u, v, w, max u (max v w)} P
  let Aut := P.gOneJointRawAutGroup j K
  let psi : A → GOneJointRawCarrier P :=
    P.gOneJointRawOldMap j
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
  exact ⟨j, K, Phi, hid, hcomp, hold⟩

end RawRectanglePresentation

end SemigenericEPPA
