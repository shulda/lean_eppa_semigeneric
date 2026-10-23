import SemigenericEPPA.Structure.DLFOneFaithfulSafeRawEPPA
import SemigenericEPPA.Structure.DLFFullRawAutSafeCofinalCover

/-!
# Complete finite safe-group extension from one good affine orbit

This composes TWO certified mathematical constructions:

(1) Relative raw EPPA under a single complete good affine orbit:
for an arbitrary larger old P and a selected induced S carrying a
faithful safe H-action, one finite genuine original-language
R1--R3 raw witness P0 extends the selected H action and separately
extends ALL partial raw isomorphisms of the whole original P.

(2) The relative graph/chain involution-killing cover for the FULL
finite raw automorphism group Q=Aut_raw(P0). One regular new
equivalence class realizes its cover group faithfully and safely,
while its projection onto Q permits ALL P0 automorphism connectors.

The output is ONE finite raw presentation W, a finite subgroup
K ≤ Aut_raw(W), a faithful homomorphism H→K extending the old
selected action, ALL old partial maps individually realized inside
K, and global complete-good-orbit safety for EVERY K involution.

This is the finite semi-coherent DLF extension step. It does not
claim that the connectors themselves are coherent, a Fraïssé
limit exists, or that its automorphism group has a DLF subgroup.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {H : Type t} [Group H] [Finite H]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- One complete good congruence orbit suffices for the finite
safe-group EPPA extension property in the ACTUAL R1--R3 language.

There is one enlarged raw structure, one finite globally-safe
automorphism subgroup K, and one faithful H→K extending the old
induced H-action on S⊆A. Every partial raw isomorphism of ALL
of A individually extends via a member of that same K. -/
theorem exists_finiteSafeGroupEPPAExtension_of_completeGoodOrbit
    (P : RawRectanglePresentation d A)
    (hGoodOrbit : d.HasCompleteGoodOrbit)
    (S : Set A) (rhoS : H →* Equiv.Perm S)
    (hFaithful : Function.Injective rhoS)
    (hPartOld : ∀ (h : H) (x y : S),
      P.part (rhoS h x).val (rhoS h y).val ↔
        P.part x.val y.val)
    (hColourOld : ∀ (h : H) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val)
    (hOldSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : S), ¬P.part x.val y.val →
        rhoS h x = y → rhoS h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x.val y.val)) :
    ∃ (W : Type (max u (max v (max w t))))
      (Pnew : RawRectanglePresentation d W)
      (e : A → W)
      (K : Subgroup Pnew.fullRawAutGroup)
      (theta : H →* K),
      Finite W ∧
      Finite K ∧
      Function.Injective e ∧
      (∀ x y : A, Pnew.part (e x) (e y) ↔ P.part x y) ∧
      (∀ x y : A, Pnew.colour (e x) (e y) = P.colour x y) ∧
      Function.Injective theta ∧
      (∀ (h : H) (x : S),
        (theta h).val.val (e x.val) = e (rhoS h x).val) ∧
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
  obtain ⟨W0, P0, e0, hFiniteW0, hE0Inj,
      hE0Part, hE0Colour,
      ⟨rho0, hRhoInj, hRhoOld, hRhoPart, hRhoRel, hRhoSafe⟩,
      hPartial0⟩ :=
    P.exists_faithfulGloballySafeRawEPPA_of_completeGoodOrbit
      hGoodOrbit S rhoS hFaithful hPartOld hColourOld hOldSafe
  letI : Finite W0 := hFiniteW0
  let rhoRaw : H →* P0.fullRawAutGroup :=
    binaryRawAutHom P0.part
      (fun c x y => P0.colour x y = some c) rho0
      (by
        intro h
        constructor
        · exact hRhoPart h
        · intro c x y
          simpa only [P0.rawRel_toStructure] using hRhoRel h c x y)
  have hRhoColour : ∀ (h : H) (x y : W0),
      P0.colour (rho0 h x) (rho0 h y) = P0.colour x y := by
    intro h x y
    exact P0.fullRawAutGroup_colour (rhoRaw h) x y
  let c0 : C := Classical.choose (d.phi_surjective 1)
  let Q := P0.fullRawAutGroup
  let f : H →* Q := P0.fullRawAutHom rho0 hRhoPart hRhoColour
  let Hsub : Subgroup Q := f.range
  let T := RelativeDLF.relativeBoundaryCover Hsub
  let Pplus : RawRectanglePresentation d (W0 ⊕ T) :=
    P0.adjoinConstantNewPart (R := T) c0
  obtain ⟨hFiniteT, K, theta, hFiniteK,
      hThetaInj, hThetaOld, hKSafe, hAllQ⟩ :=
    P0.fullRawAut_exists_finiteSafeCofinalCover
      c0 rho0 hRhoPart hRhoColour hRhoInj hRhoSafe
  letI : Finite T := hFiniteT
  have hFiniteNew : Finite (W0 ⊕ T) := inferInstance
  let e : A → W0 ⊕ T := fun x => Sum.inl (e0 x)
  have hEInj : Function.Injective e := by
    intro x y hh
    apply hE0Inj
    exact Sum.inl.inj hh
  have hEPart : ∀ x y : A,
      Pplus.part (e x) (e y) ↔ P.part x y := by
    intro x y
    change P0.part (e0 x) (e0 y) ↔ P.part x y
    exact hE0Part x y
  have hEColour : ∀ x y : A,
      Pplus.colour (e x) (e y) = P.colour x y := by
    intro x y
    change P0.colour (e0 x) (e0 y) = P.colour x y
    exact hE0Colour x y
  have hThetaOnOld : ∀ (h : H) (x : S),
      (theta h).val.val (e x.val) = e (rhoS h x).val := by
    intro h x
    change (theta h).val.val (.inl (e0 x.val)) =
      (Sum.inl (e0 (rhoS h x).val) : W0 ⊕ T)
    rw [hThetaOld h (e0 x.val), hRhoOld h x]
  have hOldPartialInK :
      ∀ (T0 : Set A) (p : T0 → A),
        Function.Injective p →
        (∀ x y : T0, P.part x.val y.val ↔ P.part (p x) (p y)) →
        (∀ x y : T0, P.colour (p x) (p y) = P.colour x.val y.val) →
        ∃ k : K, ∀ x : T0,
          k.val.val (e x.val) = e (p x) := by
    intro T0 p hp hPpart hPcolour
    obtain ⟨beta, hBetaOld, hBetaPart, hBetaRel⟩ :=
      hPartial0 T0 p hp hPpart hPcolour
    let q : Q := ⟨beta, by
      constructor
      · exact hBetaPart
      · intro c X Y
        simpa only [P0.rawRel_toStructure] using hBetaRel c X Y⟩
    obtain ⟨k, hk⟩ := hAllQ q
    refine ⟨k, ?_⟩
    intro x
    change k.val.val (.inl (e0 x.val)) =
      (Sum.inl (e0 (p x)) : W0 ⊕ T)
    rw [hk (e0 x.val)]
    change (Sum.inl (beta (e0 x.val)) : W0 ⊕ T) =
      Sum.inl (e0 (p x))
    rw [hBetaOld x]
  exact ⟨W0 ⊕ T, Pplus, e, K, theta,
    hFiniteNew, hFiniteK, hEInj,
    hEPart, hEColour, hThetaInj,
    hThetaOnOld, hKSafe, hOldPartialInK⟩

end RawRectanglePresentation
end SemigenericEPPA
