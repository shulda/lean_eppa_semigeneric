import SemigenericEPPA.Bridge.OccupiedOrbitProjectionFlipSafety
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Relative DLF: transferred complete-good-orbit safety via occupied projections

The coherent EPPA proof uses global congruence saturation to make
every H-swapped witness edge raw-safe. For relative DLF we need the
strictly WEAKER assertion: if h∈H is an actual involution and
interchanges an effective cross-E pair, its effective colour
belongs to ONE complete good congruence orbit.

An occupied-only equivariant projection sends every swapped cross
witness pair to a genuine old cross-pair swapped by the SAME h.
Assume the old action is locally safe only for involutions, and
assume each actually swapped witness colour is an affine congruence
translate of its projected old colour.

The certified congruence-invariance of GoodCompleteOrbitAt transfers
this local safety to the witness pair without any global saturation
of self-reversing effective fibres, no h²=1 assumption for an
arbitrary H element, and no H-invariance of colours outside the
old selected induced structure.

This is the key DIFFERENT-original-index geometric relative DLF
flip gate. The SAME-original-index case is separately certified
using one fixed good skeleton from the complete orbit.
-/

namespace SemigenericEPPA

universe u v w z t q
variable {H : Type u} [Group H]
variable {I : Type v} {W : Type w}
variable {G : Type z} [Group G]
variable {C : Type t} {V : Type q}

/-- Occupied projection transfers the exact INVOLUTION-only
complete-good-orbit safety of old cross-pairs through any affine
congruence distortion of actual swapped witness cross colours. -/
theorem allInvolutiveFlippedCrossPairs_completeGoodOrbit_of_occupiedProjection
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (B : EffectiveGeometry d.s W)
    (rhoOld : H →* Equiv.Perm V)
    (rhoNew : H →* Equiv.Perm W)
    (iota : H →* Equiv.Perm I)
    (idx : W → I)
    (occupied : I → Prop)
    (hBpart : ∀ x y : W, B.part x y ↔ idx x = idx y)
    (hIdx : ∀ (h : H) (x : W),
      idx (rhoNew h x) = iota h (idx x))
    (hFixed : ∀ (h : H) (i : I),
      ¬occupied i → iota h i = i)
    (proj : W → Option V)
    (hSome : ∀ x : W, occupied (idx x) →
      ∃ a : V, proj x = some a)
    (hProj : ∀ (h : H) (x : W),
      proj (rhoNew h x) = Option.map (rhoOld h) (proj x))
    (hCross : ∀ (x y : W) (a b : V),
      proj x = some a → proj y = some b →
      ¬B.part x y → ¬D.part a b)
    (hOrbit : ∀ (h : H) (x y : W) (a b : V),
      proj x = some a → proj y = some b →
      ¬B.part x y →
      rhoNew h x = y → rhoNew h y = x →
      ∃ k : G, B.F x y = congruence d.s k (D.F a b))
    (hOldInvolSafe : ∀ (h : H), h * h = 1 →
      ∀ (a b : V), ¬D.part a b →
        rhoOld h a = b → rhoOld h b = a →
          d.GoodCompleteOrbitAt (D.F a b)) :
    ∀ (h : H), h * h = 1 →
      ∀ (x y : W), ¬B.part x y →
        rhoNew h x = y → rhoNew h y = x →
          d.GoodCompleteOrbitAt (B.F x y) := by
  intro h htwo x y hxy hswapx hswapy
  have hidx : idx x ≠ idx y := by
    intro heq
    exact hxy ((hBpart x y).mpr heq)
  obtain ⟨hOccx, hOccy⟩ :=
    flippedCrossPart_occupied idx rhoNew iota occupied
      hIdx hFixed h x y hidx hswapx
  obtain ⟨a, ha⟩ := hSome x hOccx
  obtain ⟨b, hb⟩ := hSome y hOccy
  have hab : ¬D.part a b :=
    hCross x y a b ha hb hxy
  have hax : rhoOld h a = b := by
    have heq : some b = some (rhoOld h a) := by
      calc
        some b = proj y := hb.symm
        _ = proj (rhoNew h x) :=
          congrArg proj hswapx.symm
        _ = Option.map (rhoOld h) (proj x) := hProj h x
        _ = some (rhoOld h a) := by rw [ha]; rfl
    exact (Option.some.inj heq).symm
  have hby : rhoOld h b = a := by
    have heq : some a = some (rhoOld h b) := by
      calc
        some a = proj x := ha.symm
        _ = proj (rhoNew h y) :=
          congrArg proj hswapy.symm
        _ = Option.map (rhoOld h) (proj y) := hProj h y
        _ = some (rhoOld h b) := by rw [hb]; rfl
    exact (Option.some.inj heq).symm
  have hOldGood : d.GoodCompleteOrbitAt (D.F a b) :=
    hOldInvolSafe h htwo a b hab hax hby
  obtain ⟨k, hcol⟩ :=
    hOrbit h x y a b ha hb hxy hswapx hswapy
  rw [hcol]
  exact d.goodCompleteOrbitAt_congruence
    (D.F a b) k hOldGood

end SemigenericEPPA
