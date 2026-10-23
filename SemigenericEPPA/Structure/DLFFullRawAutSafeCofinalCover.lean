import SemigenericEPPA.Structure.DLFFiniteSafeRawGroupPackage
import SemigenericEPPA.Structure.DLFFiniteCoverAuxiliaryInstances
import SemigenericEPPA.Structure.DLFSafeFullRawAutRange
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Basic

/-!
# One finite safe faithful enlargement surjects onto full old raw Aut(P)

This is the purely finite group-theoretic cofinality step of DLF.

Take a finite original R1--R3 raw structure P and a genuinely
faithful raw H-action on its whole vertex set, whose H-involutions
reverse only cross-E pairs with complete good affine congruence
orbits. Let Q be the ACTUAL full raw automorphism group of P,
and Hbar ≤ Q the literal image of H. Relative F₂-chain covering
and one new regular E-class produce a finite enlarged raw Pplus,
with a finite subgroup K ≤ Aut_raw(Pplus) satisfying:

* a faithful strict H → K with precisely the original H action
  on the old P summand;
* every K involution reversing a crossed pair of Pplus is safe;
* EVERY old full raw automorphism q∈Q is realized on old P by
  SOME member of K. Hence all old partial maps with individual
  Q extensions remain simultaneously extendable within K.

The conclusion concerns the full original E/R_c language. It
does not assume full global good-fibre saturation or a fictional
H-action on a larger prescribed old witness. The latter is supplied
by the separately certified relative safe raw EPPA theorem.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {H : Type t} [Group H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Every faithful locally involution-safe subgroup of the finite
original raw automorphism group extends to a finite globally safe
subgroup of an enlarged original raw automorphism group. This new
group acts faithfully and surjects onto ALL old raw automorphisms
by restriction to the old summand. -/
theorem fullRawAut_exists_finiteSafeCofinalCover
    (P : RawRectanglePresentation d V)
    [Finite V]
    (c0 : C)
    (rho : H →* Equiv.Perm V)
    (hPart : ∀ (h : H) (x y : V),
      P.part (rho h x) (rho h y) ↔ P.part x y)
    (hColour : ∀ (h : H) (x y : V),
      P.colour (rho h x) (rho h y) = P.colour x y)
    (hFaithful : Function.Injective rho)
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rho h x = y → rho h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y)) :
    let Q := P.fullRawAutGroup
    let f := P.fullRawAutHom rho hPart hColour
    let Hsub : Subgroup Q := f.range
    let T := RelativeDLF.relativeBoundaryCover Hsub
    let Pplus := P.adjoinConstantNewPart (R := T) c0
    Finite T ∧
      ∃ (K : Subgroup Pplus.fullRawAutGroup)
        (theta : H →* K),
        Finite K ∧
        Function.Injective theta ∧
        (∀ (h : H) (x : V),
          (theta h).val.val (.inl x) = (.inl (rho h x) : V ⊕ T)) ∧
        (∀ (k : K), k * k = 1 →
          ∀ (X Y : V ⊕ T), ¬Pplus.part X Y →
            k.val.val X = Y → k.val.val Y = X →
              d.GoodCompleteOrbitAt (Pplus.effectiveReduct.F X Y)) ∧
        (∀ (q : Q), ∃ k : K,
          ∀ x : V,
            k.val.val (.inl x) = (.inl (q.val x) : V ⊕ T)) := by
  classical
  let Q := P.fullRawAutGroup
  letI : Finite Q := P.finite_fullRawAutGroup
  let f : H →* Q := P.fullRawAutHom rho hPart hColour
  have hFInj : Function.Injective f :=
    P.fullRawAutHom_injective rho hPart hColour hFaithful
  let Hsub : Subgroup Q := f.range
  let rhoQ : Q →* Equiv.Perm V := P.fullRawAutAction
  have hQPart : ∀ (q : Q) (x y : V),
      P.part (rhoQ q x) (rhoQ q y) ↔ P.part x y := by
    intro q x y
    exact P.fullRawAutGroup_part q x y
  have hQColour : ∀ (q : Q) (x y : V),
      P.colour (rhoQ q x) (rhoQ q y) = P.colour x y := by
    intro q x y
    exact P.fullRawAutGroup_colour q x y
  have hHSafe : ∀ (h : Hsub), h * h = 1 →
      ∀ (x y : V), ¬P.part x y →
        rhoQ h.val x = y → rhoQ h.val y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x y) := by
    intro h hh x y hxy hx hy
    exact P.fullRawAutHom_range_involutionSafe
      rho hPart hColour hFaithful hSafe
      h hh x y hxy hx hy
  -- The two finite graph orders come from the auxiliary (non-language)
  -- instances; using the same choices in the statement and proof is
  -- necessary because they also parameterize the exact boundary cover.
  let T := RelativeDLF.relativeBoundaryCover Hsub
  let Pplus : RawRectanglePresentation d (V ⊕ T) :=
    P.adjoinConstantNewPart (R := T) c0
  obtain ⟨hTFinite, hSurj, _hSecInj, act,
      hActInj, hActOld, _hActSec, hActSafe⟩ :=
    RelativeDLF.finiteSafeSplitRawAutPackage
      Hsub P c0 rhoQ hQPart hQColour hHSafe
  letI : Finite T := hTFinite
  letI : Finite (V ⊕ T) := inferInstance
  letI : Finite Pplus.fullRawAutGroup :=
    Pplus.finite_fullRawAutGroup
  let K : Subgroup Pplus.fullRawAutGroup := act.range
  letI : Finite K := inferInstance
  let thetaT : H →* T :=
    (RelativeDLF.relativeCoverSection Hsub).comp f.rangeRestrict
  let thetaK : H →* K := act.rangeRestrict.comp thetaT
  have hProj (h : H) :
      RelativeDLF.relativeCoverProjection Hsub (thetaT h) = f h := by
    change RelativeDLF.relativeCoverProjection Hsub
      (RelativeDLF.relativeCoverSection Hsub (f.rangeRestrict h)) = f h
    rw [RelativeDLF.relativeCoverProjection_section]
    rfl
  have hThetaInj : Function.Injective thetaK := by
    intro h k heq
    apply hFInj
    have heqAct : act (thetaT h) = act (thetaT k) :=
      congrArg Subtype.val heq
    have heqT : thetaT h = thetaT k := hActInj heqAct
    calc
      f h = RelativeDLF.relativeCoverProjection Hsub (thetaT h) :=
        (hProj h).symm
      _ = RelativeDLF.relativeCoverProjection Hsub (thetaT k) := by rw [heqT]
      _ = f k := hProj k
  have hThetaOld : ∀ (h : H) (x : V),
      (thetaK h).val.val (.inl x) =
        (.inl (rho h x) : V ⊕ T) := by
    intro h x
    change (act (thetaT h)).val (.inl x) =
      (Sum.inl (rho h x) : V ⊕ T)
    rw [hActOld (thetaT h) x, hProj h]
    rfl
  have hKSafe : ∀ (k : K), k * k = 1 →
      ∀ (X Y : V ⊕ T), ¬Pplus.part X Y →
        k.val.val X = Y → k.val.val Y = X →
          d.GoodCompleteOrbitAt (Pplus.effectiveReduct.F X Y) := by
    intro k hk X Y hcross hx hy
    obtain ⟨a, ha⟩ : ∃ a : T, act a = k.val := k.property
    have haTwo : a * a = 1 := by
      apply hActInj
      calc
        act (a * a) = act a * act a := map_mul act a a
        _ = k.val * k.val := by rw [ha]
        _ = 1 := congrArg Subtype.val hk
        _ = act 1 := (map_one act).symm
    have hPerm : (act a).val = k.val.val := congrArg Subtype.val ha
    have hx' : (act a).val X = Y := by rw [hPerm]; exact hx
    have hy' : (act a).val Y = X := by rw [hPerm]; exact hy
    exact hActSafe a haTwo X Y hcross hx' hy'
  have hAllQ : ∀ (q : Q), ∃ k : K,
      ∀ x : V,
        k.val.val (.inl x) = (.inl (q.val x) : V ⊕ T) := by
    intro q
    obtain ⟨a, ha⟩ := hSurj q
    refine ⟨⟨act a, ⟨a, rfl⟩⟩, ?_⟩
    intro x
    change (act a).val (.inl x) = (Sum.inl (q.val x) : V ⊕ T)
    rw [hActOld a x, ha]
    rfl
  exact ⟨hTFinite, K, thetaK, inferInstance,
    hThetaInj, hThetaOld, hKSafe, hAllQ⟩

end RawRectanglePresentation
end SemigenericEPPA
