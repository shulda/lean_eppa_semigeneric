import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitRawRectangle
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitRawAction
import SemigenericEPPA.Structure.DLFSemiCoherentUnrestrictedTowerLimitActionFaithful
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import Mathlib.Algebra.Group.Action.End

/-!
# Unrestricted semi-coherent actual automorphism limit: LimitAutHom

The stagewise safe-pair colimit theorem is replayed on an arbitrary
finite original-raw group-action tower. Its proof only uses strict
finite subgroup actions, induced E/R_c embeddings and the
next-stage partial connector property, not local involution safety.
No claim of tower existence is made in this module.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteRawActionPairTower

/-- The group quotient colimit acts by genuine automorphisms of the
original infinite E/R_c structure. This is a strict group
homomorphism into the literal raw-automorphism subgroup. -/
noncomputable def limitRawAutHom
    (T : FiniteRawActionPairTower d V) :
    T.GroupLimit →* T.limitRawPresentation.fullRawAutGroup := by
  letI : MulAction T.GroupLimit T.VertexLimit := T.limitMulAction
  let rho : T.GroupLimit →* Equiv.Perm T.VertexLimit :=
    MulAction.toPermHom T.GroupLimit T.VertexLimit
  have hPart : ∀ (g : T.GroupLimit) (x y : T.VertexLimit),
      T.limitRawPresentation.part (rho g x) (rho g y) ↔
        T.limitRawPresentation.part x y := by
    intro g x y
    change T.limitPart (T.limitAct g x) (T.limitAct g y) ↔
      T.limitPart x y
    exact T.limitAct_part_iff g x y
  have hColour : ∀ (g : T.GroupLimit) (x y : T.VertexLimit),
      T.limitRawPresentation.colour (rho g x) (rho g y) =
        T.limitRawPresentation.colour x y := by
    intro g x y
    change T.limitColour (T.limitAct g x) (T.limitAct g y) =
      T.limitColour x y
    exact T.limitAct_colour_eq g x y
  exact T.limitRawPresentation.fullRawAutHom rho hPart hColour

/-- The true group-colimit automorphism extends the literal old
finite-stage vertex permutation on the canonical old images. -/
theorem limitRawAutHom_apply_vertexOf
    (T : FiniteRawActionPairTower d V)
    (i : ℕ) (h : (T.stage i).subgroup) (x : V i) :
    (T.limitRawAutHom (T.groupOf i h)).val (T.vertexOf i x) =
      T.vertexOf i (h.val.val x) := by
  change T.limitAct (T.groupOf i h) (T.vertexOf i x) =
    T.vertexOf i (h.val.val x)
  exact T.limitAct_of i h x

/-- No nonidentity element of the group quotient limit is lost:
the action embeds the actual locally finite group into the actual
automorphism group of the infinite original-language structure. -/
theorem limitRawAutHom_injective
    (T : FiniteRawActionPairTower d V) :
    Function.Injective T.limitRawAutHom := by
  intro g h hgh
  have hPerm : (T.limitRawAutHom g).val =
      (T.limitRawAutHom h).val :=
    congrArg Subtype.val hgh
  have hAgree : ∀ x : T.VertexLimit,
      T.limitAct g x = T.limitAct h x := by
    intro x
    have heval := congrArg
      (fun p : Equiv.Perm T.VertexLimit => p x) hPerm
    change T.limitAct g x = T.limitAct h x at heval
    exact heval
  have hFix : ∀ x : T.VertexLimit,
      T.limitAct (g * h⁻¹) x = x := by
    intro x
    calc
      T.limitAct (g * h⁻¹) x =
          T.limitAct g (T.limitAct h⁻¹ x) :=
        T.limitAct_mul g h⁻¹ x
      _ = T.limitAct h (T.limitAct h⁻¹ x) :=
        hAgree (T.limitAct h⁻¹ x)
      _ = T.limitAct (h * h⁻¹) x :=
        (T.limitAct_mul h h⁻¹ x).symm
      _ = x := by
        simpa only [mul_inv_cancel] using T.limitAct_one x
  have hOne : g * h⁻¹ = 1 := T.limitAct_faithful (g * h⁻¹) hFix
  exact mul_inv_eq_one.mp hOne

end FiniteRawActionPairTower
end SemigenericEPPA
