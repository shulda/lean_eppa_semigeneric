import SemigenericEPPA.Structure.DLFFiniteSafeGroupEPPAExtension
import SemigenericEPPA.Structure.DLFOldPartCloneExtension

/-!
# Relative safe-group EPPA from an ACTUAL finite raw subgroup action

The positive DLF iteration starts with a finite raw presentation P,
an induced old subset S⊆P, and a finite subgroup H of the ACTUAL
original-language automorphism group of P induced on S.
The certified general theorem #428 takes instead a monoid hom
H→Perm(S) and separate proofs that it preserves all raw colours.

Here we construct those inputs canonically: restrict P by the
literal raw pullback along S↪P, take H as a subgroup of its
full E/R_c automorphism group, and use its natural evaluation action.
This action is automatically faithful and preserves every raw
predicate. Only its local complete-orbit involution safety is
left as a genuine mathematical hypothesis.

The output retains the exact full positive finite DLF content:
one finite raw witness W containing the FULL old P, a finite
safe subgroup K≤Aut_raw(W), a faithful homomorphism H→K extending
the old subgroup action on S, and all partial original raw
isomorphisms of P extended by elements of this same K.

This interface eliminates auxiliary action/faithfulness witnesses
when iterating finite safe pairs. It does not build the limit.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {V : Type w} [Fintype V]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- An actual subgroup of the original raw automorphisms of an
induced old S, assumed locally safe, admits a finite raw extension
whose SAME finite safe automorphism subgroup extends the old
action and ALL partial maps of the WHOLE old P. -/
theorem exists_finiteSafeGroupEPPAExtension_of_rawSubgroup
    (P : RawRectanglePresentation d V)
    (hOrbit : d.HasCompleteGoodOrbit)
    (S : Set V)
    (H : Subgroup
      ((P.pullbackRaw (fun x : S => x.val)).fullRawAutGroup))
    (hSafe : ∀ (h : H), h * h = 1 →
      ∀ (x y : S), ¬P.part x.val y.val →
        h.val.val x = y → h.val.val y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x.val y.val)) :
    ∃ (W : Type (max u (max v w)))
      (Pnew : RawRectanglePresentation d W)
      (e : V → W)
      (K : Subgroup Pnew.fullRawAutGroup)
      (theta : H →* K),
      Finite W ∧
      Finite K ∧
      Function.Injective e ∧
      (∀ x y : V, Pnew.part (e x) (e y) ↔ P.part x y) ∧
      (∀ x y : V, Pnew.colour (e x) (e y) = P.colour x y) ∧
      Function.Injective theta ∧
      (∀ (h : H) (x : S),
        (theta h).val.val (e x.val) = e (h.val.val x).val) ∧
      (∀ (k : K), k * k = 1 →
        ∀ (X Y : W), ¬Pnew.part X Y →
          k.val.val X = Y → k.val.val Y = X →
            d.GoodCompleteOrbitAt (Pnew.effectiveReduct.F X Y)) ∧
      (∀ (T : Set V) (p : T → V),
        Function.Injective p →
        (∀ x y : T, P.part x.val y.val ↔ P.part (p x) (p y)) →
        (∀ x y : T, P.colour (p x) (p y) = P.colour x.val y.val) →
        ∃ k : K, ∀ x : T,
          k.val.val (e x.val) = e (p x)) := by
  classical
  let PS : RawRectanglePresentation d S :=
    P.pullbackRaw (fun x : S => x.val)
  letI : Finite PS.fullRawAutGroup := PS.finite_fullRawAutGroup
  letI : Finite H := inferInstance
  let rhoS : H →* Equiv.Perm S :=
    PS.fullRawAutAction.comp H.subtype
  have hFaithful : Function.Injective rhoS := by
    intro h k hh
    apply Subtype.ext
    apply Subtype.ext
    exact hh
  have hPart : ∀ (h : H) (x y : S),
      P.part (rhoS h x).val (rhoS h y).val ↔
        P.part x.val y.val := by
    intro h x y
    change PS.part (h.val.val x) (h.val.val y) ↔ PS.part x y
    exact PS.fullRawAutGroup_part h.val x y
  have hColour : ∀ (h : H) (x y : S),
      P.colour (rhoS h x).val (rhoS h y).val =
        P.colour x.val y.val := by
    intro h x y
    change PS.colour (h.val.val x) (h.val.val y) =
      PS.colour x y
    exact PS.fullRawAutGroup_colour h.val x y
  have hSafeRho : ∀ (h : H), h * h = 1 →
      ∀ (x y : S), ¬P.part x.val y.val →
        rhoS h x = y → rhoS h y = x →
          d.GoodCompleteOrbitAt (P.effectiveReduct.F x.val y.val) := by
    intro h hh x y hxy hX hY
    exact hSafe h hh x y hxy hX hY
  exact P.exists_finiteSafeGroupEPPAExtension_of_completeGoodOrbit
    hOrbit S rhoS hFaithful hPart hColour hSafeRho

end RawRectanglePresentation
end SemigenericEPPA
