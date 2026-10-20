import SemigenericEPPA.Bridge.OccupiedProjectionFlipSafety
import SemigenericEPPA.Algebra.CongruenceAction

/-!
# Raw flip safety through an occupied projection UP TO congruence orbit

For G=1 the fixed factorial copied-fibre witness has the same
effective cross-colour as the old pair obtained by the canonical
equivariant projection. That gave the certified exact-colour
flip-safety theorem of OccupiedProjectionFlipSafety.

For nontrivial G the correct condition is weaker: a flipped
witness cross pair projects to an ACTUAL old swapped cross pair
but its effective colour can differ from the old colour by an
AFFINE CONGRUENCE translation. This is precisely what the
gauge multipliers M^h_{ij} do in the main manuscript.

If the good effective-colour set S is globally congruence-saturated,
a genuinely self-reversing raw representative at the projected
old colour guarantees one at the witness colour.

This theorem works in ANY nonabelian group with arbitrary affine
anti-involution and ANY H element exchanging the two witness
vertices, not just involutions. An equivariant Option-valued
projection is required ONLY on occupied E-parts: unoccupied
part indices are fixed pointwise, preventing artificial flips.

The geometric existence of such a projection and its orbit-valued
colour relation for the full nontrivial-G valuation witness is
a subsequent construction.
-/

namespace SemigenericEPPA

universe u v w z t q

variable {H : Type u} [Group H]
variable {I : Type v} {W : Type w}
variable {G : Type z} [Group G] {C : Type t} {V : Type q}

/-- Generalized safe raw-cover lift criterion: actual H-equivariant
old projections on occupied E-parts and effective witness colours
in the SAME affine congruence orbit as those old pairs suffice
for ALL exchanged cross-E witness pairs, provided the full
set of good raw-colour fibres is congruence-saturated. -/
theorem allFlippedCrossPairs_safe_of_occupiedOrbitProjection
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (B : EffectiveGeometry d.s W)
    (old : V → V → C)
    (hPhi : ∀ x y : V, ¬D.part x y →
      d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y : V, ¬D.part x y →
      old y x = d.reverse (old x y))
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
    (hOrbit : ∀ (x y : W) (a b : V),
      proj x = some a → proj y = some b →
      ¬B.part x y →
      ∃ k : G, B.F x y = congruence d.s k (D.F a b))
    (hRaw : ∀ (h : H) (a b : V), ¬D.part a b →
      old (rhoOld h a) (rhoOld h b) = old a b)
    (hsat : d.IsCongruenceSaturated) :
    ∀ (h : H) (x y : W), ¬B.part x y →
      rhoNew h x = y → rhoNew h y = x →
      ∃ c : C, d.phi c = B.F x y ∧ d.reverse c = c := by
  intro h x y hxy hswapx hswapy
  have hidx : idx x ≠ idx y := by
    intro heq
    exact hxy ((hBpart x y).mpr heq)
  obtain ⟨hOccx, hOccy⟩ :=
    flippedCrossPart_occupied idx rhoNew iota occupied
      hIdx hFixed h x y hidx hswapx
  obtain ⟨a, ha⟩ := hSome x hOccx
  obtain ⟨b, hb⟩ := hSome y hOccy
  have hab : ¬D.part a b := hCross x y a b ha hb hxy
  have hax : rhoOld h a = b := by
    have heq : some b = some (rhoOld h a) := by
      calc
        some b = proj y := hb.symm
        _ = proj (rhoNew h x) := congrArg proj hswapx.symm
        _ = Option.map (rhoOld h) (proj x) := hProj h x
        _ = some (rhoOld h a) := by rw [ha]; rfl
    exact (Option.some.inj heq).symm
  have hby : rhoOld h b = a := by
    have heq : some a = some (rhoOld h b) := by
      calc
        some a = proj x := ha.symm
        _ = proj (rhoNew h y) := congrArg proj hswapy.symm
        _ = Option.map (rhoOld h) (proj y) := hProj h y
        _ = some (rhoOld h b) := by rw [hb]; rfl
    exact (Option.some.inj heq).symm
  have hInv : old b a = old a b := by
    have hpres := hRaw h a b hab
    rw [hax, hby] at hpres
    exact hpres
  have hgood : D.F a b ∈ d.selfReverseEffective :=
    ⟨old a b, hPhi a b hab,
      (hReverse a b hab).symm.trans hInv⟩
  obtain ⟨k, hcol⟩ := hOrbit x y a b ha hb hxy
  have hwgood : congruence d.s k (D.F a b) ∈
      d.selfReverseEffective :=
    hsat k (D.F a b) hgood
  rw [←hcol] at hwgood
  exact hwgood

/-- **Minimal flip-only orbit interface.** To prove raw flip-safety
for an arbitrary nonabelian effective group, it suffices that the
effective witness colour is in the congruence orbit of the old
projected effective colour ONLY WHEN some H-element actually swaps
the two witness vertices. It is NOT necessary (and generally
unwarranted) to demand orbit agreement for every cross-part pair.

The old raw reference is genuinely invariant, and the projected
old pair becomes swapped under the same h by H-equivariance of
the partial projection. Consequently its raw colour is fixed by
reversal; congruence saturation transports that goodness to the
specific swapped witness colour. No unoccupied old projections
or h²=1 hypothesis. -/
theorem allFlippedCrossPairs_safe_of_swappedOccupiedOrbitProjection
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (B : EffectiveGeometry d.s W)
    (old : V → V → C)
    (hPhi : ∀ x y : V, ¬D.part x y →
      d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y : V, ¬D.part x y →
      old y x = d.reverse (old x y))
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
    (hRaw : ∀ (h : H) (a b : V), ¬D.part a b →
      old (rhoOld h a) (rhoOld h b) = old a b)
    (hsat : d.IsCongruenceSaturated) :
    ∀ (h : H) (x y : W), ¬B.part x y →
      rhoNew h x = y → rhoNew h y = x →
      ∃ c : C, d.phi c = B.F x y ∧ d.reverse c = c := by
  intro h x y hxy hswapx hswapy
  have hidx : idx x ≠ idx y := by
    intro heq
    exact hxy ((hBpart x y).mpr heq)
  obtain ⟨hOccx, hOccy⟩ :=
    flippedCrossPart_occupied idx rhoNew iota occupied
      hIdx hFixed h x y hidx hswapx
  obtain ⟨a, ha⟩ := hSome x hOccx
  obtain ⟨b, hb⟩ := hSome y hOccy
  have hab : ¬D.part a b := hCross x y a b ha hb hxy
  have hax : rhoOld h a = b := by
    have heq : some b = some (rhoOld h a) := by
      calc
        some b = proj y := hb.symm
        _ = proj (rhoNew h x) := congrArg proj hswapx.symm
        _ = Option.map (rhoOld h) (proj x) := hProj h x
        _ = some (rhoOld h a) := by rw [ha]; rfl
    exact (Option.some.inj heq).symm
  have hby : rhoOld h b = a := by
    have heq : some a = some (rhoOld h b) := by
      calc
        some a = proj x := ha.symm
        _ = proj (rhoNew h y) := congrArg proj hswapy.symm
        _ = Option.map (rhoOld h) (proj y) := hProj h y
        _ = some (rhoOld h b) := by rw [hb]; rfl
    exact (Option.some.inj heq).symm
  have hInv : old b a = old a b := by
    have hpres := hRaw h a b hab
    rw [hax, hby] at hpres
    exact hpres
  have hgood : D.F a b ∈ d.selfReverseEffective :=
    ⟨old a b, hPhi a b hab,
      (hReverse a b hab).symm.trans hInv⟩
  obtain ⟨k, hcol⟩ :=
    hOrbit h x y a b ha hb hxy hswapx hswapy
  have hwgood : congruence d.s k (D.F a b) ∈
      d.selfReverseEffective :=
    hsat k (D.F a b) hgood
  rw [←hcol] at hwgood
  exact hwgood


end SemigenericEPPA
