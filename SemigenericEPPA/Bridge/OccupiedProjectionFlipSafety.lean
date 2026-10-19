import SemigenericEPPA.Bridge.ProjectedFlipSafety

/-!
# Flip safety via a projection defined only on occupied E-parts

A globally equivariant map from the entire padded carrier to the selected
old substructure is generally impossible: unoccupied E-classes have no
selected old vertices.  It is also unnecessary.

Suppose a group H acts on witness vertices and E-part indices, and fixes
every UNoccupied index.  Then a cross-part pair exchanged by h necessarily
lies in two occupied parts.  We can project just those vertices to actual
old vertices, using an Option-valued H-equivariant map (None on the
unoccupied sector).  This gives a self-reversing old raw representative
for every flipped witness cross-edge, with no restriction h²=1.

The theorem is a precise interface for the prospective replicated-fibre
group action.  It does not assert the existence of the projection nor
claim that naive uniform padding has the necessary safety property.
-/

namespace SemigenericEPPA

universe u v w z t q

variable {H : Type u} [Group H]
variable {I : Type v} {W : Type w}
variable {G : Type z} [Group G] {C : Type t} {V : Type q}

/-- If H preserves part indices and fixes every unoccupied part,
a swapped pair in *different* E-parts must lie in occupied parts.
Only one of the swap equations is needed for this conclusion. -/
theorem flippedCrossPart_occupied
    (idx : W → I)
    (sigma : H →* Equiv.Perm W)
    (iota : H →* Equiv.Perm I)
    (occupied : I → Prop)
    (hIdx : ∀ (h : H) (x : W),
      idx (sigma h x) = iota h (idx x))
    (hFixed : ∀ (h : H) (i : I),
      ¬occupied i → iota h i = i)
    (h : H) (x y : W)
    (hcross : idx x ≠ idx y)
    (hxy : sigma h x = y) :
    occupied (idx x) ∧ occupied (idx y) := by
  have hx : occupied (idx x) := by
    by_contra hn
    have heq : idx y = idx x := by
      calc
        idx y = idx (sigma h x) := congrArg idx hxy.symm
        _ = iota h (idx x) := hIdx h x
        _ = idx x := hFixed h (idx x) hn
    exact hcross heq.symm
  have hy : occupied (idx y) := by
    by_contra hn
    have hidx : idx y = iota h (idx x) := by
      calc
        idx y = idx (sigma h x) := congrArg idx hxy.symm
        _ = iota h (idx x) := hIdx h x
    have hfix := hFixed (h⁻¹) (idx y) hn
    have heq : idx x = idx y := by
      calc
        idx x = iota h⁻¹ (iota h (idx x)) := by
          simp
        _ = iota h⁻¹ (idx y) := congrArg (iota h⁻¹) hidx.symm
        _ = idx y := hfix
    exact hcross heq
  exact ⟨hx, hy⟩

/-- The desired raw flip-safety criterion with a PARTIAL projection.
On occupied parts the projection is Some(old vertex), equivariant
under H; on other parts it may be None.  Unlike a global projection
lemma, this covers witnesses having unoccupied E-classes.

The geometric assumptions guarantee that projected cross-E pairs
are genuine old cross-E pairs and that the raw effective colour on
the lifted edge agrees with its old projected colour.  The theorem
proves safety for EVERY flipped pair, including swaps by elements
of order greater than two. -/
theorem allFlippedCrossPairs_safe_of_occupiedProjection
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
    (hColour : ∀ (x y : W) (a b : V),
      proj x = some a → proj y = some b →
      ¬B.part x y → B.F x y = D.F a b)
    (hRaw : ∀ (h : H) (a b : V), ¬D.part a b →
      old (rhoOld h a) (rhoOld h b) = old a b) :
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
  let c : C := old a b
  refine ⟨c, ?_, ?_⟩
  · calc
      d.phi c = D.F a b := hPhi a b hab
      _ = B.F x y := (hColour x y a b ha hb hxy).symm
  · have hInv : old b a = old a b := by
      have hr := hRaw h a b hab
      rw [hax, hby] at hr
      exact hr
    calc
      d.reverse c = old b a := (hReverse a b hab).symm
      _ = c := hInv

end SemigenericEPPA
