import SemigenericEPPA.Structure.DLFFiniteSafeGroupEPPAExtension
import Mathlib.Algebra.Group.PUnit

/-!
# Positive cofinal safe finite-group EPPA under one complete good orbit

The complete finite relative safe-group EPPA theorem applies to ANY
faithful locally safe finite H-action on an induced old subset.
For a plain finite raw rectangle P, take the TRIVIAL H=PUnit acting
on the EMPTY selected old subset. Its faithfulness, preservation
and local involution safety are all immediate.

Consequently, if the raw datum admits one complete good affine
congruence orbit, every finite R1--R3 raw structure P embeds into a
finite raw witness W carrying a FINITE subgroup K≤Aut_raw(W) that:
  (1) is globally complete-good-orbit-safe for every involution;
  (2) extends EVERY individual partial original raw isomorphism of
      P by an element of the SAME K on the SAME embedded old copy.

This is the cofinal initial-pair construction needed alongside the
relative extension theorem for the positive semi-coherent EP
criterion. This is stronger than ordinary EPPA but does not supply
coherent choices of connectors or an infinite DLF subgroup by itself.
-/

namespace SemigenericEPPA
open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- One complete good congruence orbit already gives a COFINAL
family of finite globally involution-safe automorphism subgroups
that extend all partial raw maps of each finite original input. -/
theorem exists_cofinalFiniteSafeGroupEPPA_of_completeGoodOrbit
    (P : RawRectanglePresentation d A)
    (hGoodOrbit : d.HasCompleteGoodOrbit) :
    ∃ (W : Type (max u (max v w)))
      (Pnew : RawRectanglePresentation d W)
      (e : A → W)
      (K : Subgroup Pnew.fullRawAutGroup),
      Finite W ∧
      Finite K ∧
      Function.Injective e ∧
      (∀ x y : A, Pnew.part (e x) (e y) ↔ P.part x y) ∧
      (∀ x y : A, Pnew.colour (e x) (e y) = P.colour x y) ∧
      (∀ (k : K), k * k = 1 →
        ∀ (X Y : W), ¬Pnew.part X Y →
          k.val.val X = Y → k.val.val Y = X →
            d.GoodCompleteOrbitAt (Pnew.effectiveReduct.F X Y)) ∧
      (∀ (T : Set A) (p : T → A),
        Function.Injective p →
        (∀ x y : T, P.part x.val y.val ↔ P.part (p x) (p y)) →
        (∀ x y : T, P.colour (p x) (p y) = P.colour x.val y.val) →
        ∃ k : K, ∀ x : T,
          k.val.val (e x.val) = e (p x)) := by
  classical
  let S : Set A := ∅
  let rhoS : PUnit →* Equiv.Perm S := 1
  have hFaithful : Function.Injective rhoS := by
    intro h k _
    exact Subsingleton.elim h k
  have hPart : ∀ (h : PUnit) (x y : S),
      P.part (rhoS h x).val (rhoS h y).val ↔
        P.part x.val y.val := by
    intro h x y
    cases x.property
  have hColour : ∀ (h : PUnit) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val := by
    intro h x y
    cases x.property
  have hSafe : ∀ (h : PUnit), h * h = 1 →
      ∀ (x y : S), ¬P.part x.val y.val →
        rhoS h x = y → rhoS h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x.val y.val) := by
    intro h hh x y
    cases x.property
  obtain ⟨W, Pnew, e, K, theta, hFiniteW, hFiniteK,
      he, hPartEmbed, hColourEmbed, _hThetaFaithful,
      _hThetaOld, hKSafe, hPartials⟩ :=
    P.exists_finiteSafeGroupEPPAExtension_of_completeGoodOrbit
      (H := PUnit) hGoodOrbit S rhoS hFaithful
      hPart hColour hSafe
  exact ⟨W, Pnew, e, K, hFiniteW, hFiniteK,
    he, hPartEmbed, hColourEmbed, hKSafe, hPartials⟩

end RawRectanglePresentation
end SemigenericEPPA
