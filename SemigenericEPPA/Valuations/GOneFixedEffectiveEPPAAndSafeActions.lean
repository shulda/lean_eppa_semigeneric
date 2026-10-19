import SemigenericEPPA.Valuations.SafeFactorialActionOnOldSubset
import SemigenericEPPA.Structure.SubsingletonFactorialEffectiveEPPA
import SemigenericEPPA.Algebra.FixedFactorialOldInjection

/-!
# A single fixed G=1 effective EPPA witness with ALL safe H-actions

The original finite raw presentation P determines its effective
E-quotient I. Fix M=|A|! and ONE old injection j:A↪Fin M BEFORE
quantifying over any partial automorphism, induced substructure or
group H. The fixed effective witness carrier is I×Fin M.

The certified uniform-fibre extension theorem supplies ordinary
partial E/F automorphism extensions on this very carrier.
Separately, the certified replicated-fibre theorem constructs safe
homomorphic H-actions on the SAME carrier for every induced old
subset S⊆A and any H-action preserving the original ordered raw
colours. The present theorem packages their existential quantifier
order into ONE reusable API.

This is an EFFECTIVE G=1 EPPA + safe-actions result. The fixed raw
cover, its universal code and the typed coherent groupoid extension
are subsequent separate obligations.
-/

namespace SemigenericEPPA

universe u v w t

variable {G : Type u} [Group G] [Subsingleton G]
variable {C : Type v} {A : Type w} [Fintype A]
variable {d : RawDatum G C}

/-- The prechosen factorial-size effective witness base for P. -/
abbrev GOneFactorialCarrier
    (P : RawRectanglePresentation d A) :=
  Quotient P.effectiveReduct.part × Fin (coherentPaddingSize A)

/-- Its genuine effective rectangle geometry, with E given exactly
by equality of the first coordinate. -/
noncomputable def RawRectanglePresentation.gOneFactorialGeometry
    (P : RawRectanglePresentation d A) :
    EffectiveGeometry d.s (GOneFactorialCarrier P) :=
  subsingletonFixedPartGeometry d.s
    (Quotient P.effectiveReduct.part) (coherentPaddingSize A)

/-- The old embedding chosen BEFORE any partial map or group H. -/
def RawRectanglePresentation.gOneFactorialOldMap
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (x : A) : GOneFactorialCarrier P :=
  (Quotient.mk P.effectiveReduct.part x, j x)

/-- Ordinary effective EPPA on that one predetermined base. -/
def RawRectanglePresentation.HasFactorialPartialExtensions
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A)) : Prop :=
  ∀ (S : Set A) (p : S → A),
    Function.Injective p →
    (∀ x y : S, P.part x.val y.val ↔ P.part (p x) (p y)) →
    ∃ pi : Equiv.Perm (GOneFactorialCarrier P),
      (∀ x : S,
        pi (P.gOneFactorialOldMap j x.val) =
          P.gOneFactorialOldMap j (p x)) ∧
      (∀ x y : GOneFactorialCarrier P,
        P.gOneFactorialGeometry.part (pi x) (pi y) ↔
          P.gOneFactorialGeometry.part x y) ∧
      (∀ x y : GOneFactorialCarrier P,
        ¬P.gOneFactorialGeometry.part x y →
        P.gOneFactorialGeometry.F (pi x) (pi y) =
          P.gOneFactorialGeometry.F x y)

/-- Every induced old S with any raw-colour-preserving H-action
extends safely and homomorphically on that same effective base. -/
def RawRectanglePresentation.HasAllFactorialSafeActions
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A)) : Prop :=
  ∀ (H : Type t) [Group H]
      (S : Set A) (rho : H →* Equiv.Perm S),
    (∀ (h : H) (x y : S),
      P.part x.val y.val ↔
        P.part (rho h x).val (rho h y).val) →
    (∀ (h : H) (x y : S),
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val) →
    ∃ theta : H →* Equiv.Perm (GOneFactorialCarrier P),
      (∀ (h : H) (x : S),
        theta h (P.gOneFactorialOldMap j x.val) =
          P.gOneFactorialOldMap j (rho h x).val) ∧
      (∀ (h : H) (x y : GOneFactorialCarrier P),
        P.gOneFactorialGeometry.part (theta h x) (theta h y) ↔
          P.gOneFactorialGeometry.part x y) ∧
      (∀ (h : H) (x y : GOneFactorialCarrier P),
        ¬P.gOneFactorialGeometry.part x y →
        P.gOneFactorialGeometry.F (theta h x) (theta h y) =
          P.gOneFactorialGeometry.F x y) ∧
      (∀ (h : H) (x y : GOneFactorialCarrier P),
        ¬P.gOneFactorialGeometry.part x y →
        theta h x = y → theta h y = x →
        ∃ c : C, d.phi c = P.gOneFactorialGeometry.F x y ∧
          d.reverse c = c)

/-- One fixed finite effective geometry with one induced old
embedding simultaneously supports every individual partial
isomorphism and every induced-substructure safe finite-group
action, with correct existential quantifier order. -/
theorem RawRectanglePresentation.exists_gOneFactorialEffectiveEPPA_andAllSafeActions
    (P : RawRectanglePresentation d A) :
    ∃ j : A → Fin (coherentPaddingSize A),
      Function.Injective (P.gOneFactorialOldMap j) ∧
      (∀ x y : A,
        P.gOneFactorialGeometry.part
          (P.gOneFactorialOldMap j x)
          (P.gOneFactorialOldMap j y) ↔ P.part x y) ∧
      P.HasFactorialPartialExtensions j ∧
      P.HasAllFactorialSafeActions j := by
  classical
  obtain ⟨j, hj⟩ := exists_fixedFactorialOldInjection A
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · exact fixedSubsingletonOldMap_injective
      P.effectiveReduct (coherentPaddingSize A) j hj
  · intro x y
    exact (fixedSubsingletonOldMap_part P.effectiveReduct
      (coherentPaddingSize A) j x y).trans
        (P.effectiveReduct_part x y)
  · intro S p hp hE
    have hE' : ∀ x y : S,
        P.effectiveReduct.part x.val y.val ↔
          P.effectiveReduct.part (p x) (p y) := by
      intro x y
      simpa only [P.effectiveReduct_part] using hE x y
    obtain ⟨pi, hOld, hPart, hF⟩ :=
      P.effectiveReduct.exists_subsingletonFixedPartPartialExtension
        (coherentPaddingSize A) j hj S p hp hE'
    exact ⟨pi, hOld, hPart, hF⟩
  · intro H inst S rho hE hRaw
    exact P.exists_safeFactorialAction_onOldSubset
      (H := H) j hj S rho hE hRaw

end SemigenericEPPA
