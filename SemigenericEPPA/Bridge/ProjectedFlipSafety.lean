import SemigenericEPPA.Structure.EffectiveGeometry

/-!
# Equivariant projection forces raw self-reversing colours on flipped edges

The positive coherent/relative-DLF group-lift step requires the safety
condition that if an element h of H interchanges two endpoints of an
effective cross-pair, its effective colour has a self-reversing raw
representative.

This safety condition follows WITHOUT ANY ASSUMPTION that h is an
involution when the endpoint action has an H-equivariant projection
onto real old vertices that preserves cross-part pairs.  Indeed, a
flipped lifted pair projects to an ACTUAL old ordered raw pair whose
two endpoints are exchanged by h.  Invariance of the old raw colour
and raw reversal then give an actual self-reversing raw representative.

This is the exact abstract flip-transfer lemma needed by a
copying/phase construction.  It does NOT construct that equivariant
projection or establish safety for an arbitrary uniform padding:
a uniform padding can have artificial flipped pairs whose labels
belong to the wrong original E-classes.
-/

namespace SemigenericEPPA

universe u v w z t

variable {G : Type u} [Group G] {C : Type v} {V : Type w}
variable {W : Type z} {H : Type t} [Group H]

/-- A flipped pair in an H-set is safe whenever it H-equivariantly
projects to a genuine cross-part old raw-coloured pair. Importantly,
this works for arbitrary h, not just elements of order two. -/
theorem projectedFlippedPair_hasSelfReversingRawColour
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s V)
    (old : V → V → C)
    (hPhi : ∀ x y : V, ¬D.part x y →
      d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y : V, ¬D.part x y →
      old y x = d.reverse (old x y))
    (rhoOld : H →* Equiv.Perm V)
    (rhoNew : H →* Equiv.Perm W)
    (proj : W → V)
    (hProj : ∀ (h : H) (x : W),
      proj (rhoNew h x) = rhoOld h (proj x))
    (hRaw : ∀ (h : H) (x y : V), ¬D.part x y →
      old (rhoOld h x) (rhoOld h y) = old x y)
    (h : H) (x y : W)
    (hcross : ¬D.part (proj x) (proj y))
    (hxy : rhoNew h x = y)
    (hyx : rhoNew h y = x) :
    ∃ c : C, d.phi c = D.F (proj x) (proj y) ∧
      d.reverse c = c := by
  let c := old (proj x) (proj y)
  refine ⟨c, hPhi (proj x) (proj y) hcross, ?_⟩
  have hx : rhoOld h (proj x) = proj y := by
    calc
      rhoOld h (proj x) = proj (rhoNew h x) :=
        (hProj h x).symm
      _ = proj y := congrArg proj hxy
  have hy : rhoOld h (proj y) = proj x := by
    calc
      rhoOld h (proj y) = proj (rhoNew h y) :=
        (hProj h y).symm
      _ = proj x := congrArg proj hyx
  have hs : old (proj y) (proj x) =
      old (proj x) (proj y) := by
    have hpres := hRaw h (proj x) (proj y) hcross
    rw [hx, hy] at hpres
    exact hpres
  calc
    d.reverse c = old (proj y) (proj x) :=
      (hReverse (proj x) (proj y) hcross).symm
    _ = c := hs

/-- A semantic structure-level version of the same flip transfer:
all flipped cross-part pairs are raw-safe provided a global
H-equivariant projection sends cross-part witness pairs to
cross-part pairs of the old geometry. -/
theorem allFlippedCrossPairs_safe_of_equivariantProjection
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
    (proj : W → V)
    (hProj : ∀ (h : H) (x : W),
      proj (rhoNew h x) = rhoOld h (proj x))
    (hCross : ∀ x y : W, ¬B.part x y →
      ¬D.part (proj x) (proj y))
    (hRaw : ∀ (h : H) (x y : V), ¬D.part x y →
      old (rhoOld h x) (rhoOld h y) = old x y) :
    ∀ (h : H) (x y : W), ¬B.part x y →
      rhoNew h x = y → rhoNew h y = x →
      ∃ c : C, d.phi c = D.F (proj x) (proj y) ∧
        d.reverse c = c := by
  intro h x y hxy hflip hflip'
  exact projectedFlippedPair_hasSelfReversingRawColour
    d D old hPhi hReverse rhoOld rhoNew proj hProj hRaw
    h x y (hCross x y hxy) hflip hflip'

end SemigenericEPPA
