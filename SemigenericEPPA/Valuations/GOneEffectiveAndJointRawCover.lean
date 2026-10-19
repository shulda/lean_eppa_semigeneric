import SemigenericEPPA.Valuations.GOneFixedEffectiveEPPAAndSafeActions
import SemigenericEPPA.Structure.FixedJointRawCover

/-!
# One universal G=1 effective witness and ONE raw cover

This theorem combines two certified existence statements with the
correct quantifier order. Fix an ORIGINAL finite raw presentation P
with trivial effective group G. Choose ONE embedding
  j : A → Fin(|A|!)
and ONE full finite raw cover over the fixed effective geometry
  (A/E) × Fin(|A|!),
BEFORE choosing any partial raw isomorphism or induced-substructure
group H.

The effective witness supports individual extensions of every
partial E-isomorphism and safe homomorphic H-actions of EVERY raw
automorphism group on any induced old subset. The SAME fixed raw
cover has the original raw structure as a literal zero-section
substructure, individually lifts any effective extension preserving
old raw labels, and homomorphically lifts every safe effective
H-action preserving the chosen old raw reference.

The theorem packages the two universal APIs without quietly
claiming that their hypotheses are discharged jointly. Those
final compositions and the exact coherent groupoid functor remain
separate obligations.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

/-- Choose one finite factorial-padded G=1 effective EPPA witness
and one raw-cover code/baseline, all before ANY subsequently chosen
partial old map or induced-substructure H-action. -/
theorem RawRectanglePresentation.exists_gOneEffectiveAndJointRawCover
    (P : RawRectanglePresentation d A) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (K : FixedJointRawCover P P.gOneFactorialGeometry
        (P.gOneFactorialOldMap j)),
      Function.Injective (P.gOneFactorialOldMap j) ∧
      (∀ x y : A,
        P.gOneFactorialGeometry.part
          (P.gOneFactorialOldMap j x)
          (P.gOneFactorialOldMap j y) ↔ P.part x y) ∧
      P.HasFactorialPartialExtensions j ∧
      P.HasAllFactorialSafeActions j := by
  classical
  obtain ⟨j, hj, hpart, hpartial, hsafegroup⟩ :=
    P.exists_gOneFactorialEffectiveEPPA_andAllSafeActions
  let V := GOneFactorialCarrier P
  letI : Finite V := inferInstance
  have hF : ∀ x y : A, ∀ c : C,
      P.colour x y = some c →
      d.phi c = P.gOneFactorialGeometry.F
        (P.gOneFactorialOldMap j x)
        (P.gOneFactorialOldMap j y) := by
    intro x y c hc
    exact Subsingleton.elim _ _
  obtain ⟨K⟩ :=
    exists_fixedJointRawCover P P.gOneFactorialGeometry
      (P.gOneFactorialOldMap j) hj hpart hF
  exact ⟨j, K, hj, hpart, hpartial, hsafegroup⟩

end SemigenericEPPA
