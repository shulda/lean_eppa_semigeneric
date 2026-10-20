import SemigenericEPPA.Bridge.RawTypedEmbedding
import SemigenericEPPA.Structure.RawPresentationEffectiveBridge

/-!
# Raw typed embeddings preserve exact effective G-colours on all cross edges

The negative congruence-orbit obstruction is formulated using a
coherent EPPA witness along an actual Structure.Embedding in the
original R1--R3 binary language. The geometry of the obstruction
uses the effective group-valued colour F.

Because original typed embeddings preserve and reflect EVERY
raw-colour predicate P_c, and F(x,y) is literally phi(c) on a
cross-part edge, effective F is preserved ON THE NOSE. There
are no assumptions about the artificial dummy values of F
within one E-part.

This small but essential bridge prevents treating effective
colour invariance as an extra hypothesis of the negative theorem.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z
variable {G : Type u} [Group G]
variable {C : Type v} {V : Type w} {W : Type z}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- The actual R1--R3 typed embedding induces exact equality of
the effective colour of every OLD cross-E ordered pair. -/
theorem effectiveColour_of_typedEmbedding
    (P : RawRectanglePresentation d V)
    (Q : RawRectanglePresentation d W)
    (psi : Structure.Embedding
      (rectangleTrivialAction C) P.toStructure Q.toStructure)
    (x y : V) (hcross : ¬P.part x y) :
    Q.effectiveReduct.F (psi x) (psi y) =
      P.effectiveReduct.F x y := by
  have hlang : psi.lang = (1 : Equiv.Perm (Fin 0)) := by
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  obtain ⟨c, hc⟩ : ∃ c : C, P.colour x y = some c := by
    cases hc : P.colour x y with
    | none =>
        exact False.elim (hcross ((P.colour_none_iff x y).mp hc))
    | some c =>
        exact ⟨c, rfl⟩
  have h := psi.map_rel_iff
    (binarySymbol C (some c)) (pairTuple x y)
  rw [hlang, Language.Action.onRel_one] at h
  change Q.colour (psi x) (psi y) = some c ↔
    P.colour x y = some c at h
  have hcQ : Q.colour (psi x) (psi y) = some c :=
    h.mpr hc
  calc
    Q.effectiveReduct.F (psi x) (psi y) = d.phi c :=
      (Q.effectiveReduct_crossColour (psi x) (psi y) c hcQ).symm
    _ = P.effectiveReduct.F x y :=
      P.effectiveReduct_crossColour x y c hc

end RawRectanglePresentation

end SemigenericEPPA
