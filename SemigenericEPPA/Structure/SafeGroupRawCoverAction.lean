import SemigenericEPPA.Bridge.GeometricInvariantRawCrossPairs
import SemigenericEPPA.Structure.InvariantRawResidualMatrix
import SemigenericEPPA.Structure.RawCoverFixedGroupLift

/-!
# The homomorphic raw-cover lift of reversal-safe finite group actions

The abstract orbit-colouring construction, its geometric cross-pair
instantiation, the canonical global affine-code encoder, the invariant
residual-matrix lemma and the fixed-cover potential action combine.

Suppose H acts by effective E/F automorphisms on a finite geometry D,
and every element of H which exchanges the endpoints of a genuine
cross-E pair has a self-reversing raw representative over that pair's
effective colour.

Choose ONE reversal-compatible raw colouring invariant under H on
all cross-pairs, and encode it to an H-invariant additive residual
matrix r. An independent baseline b gives a fixed finite raw cover
of D. The relative-potential lemma, with empty prescribed old set,
lifts H homomorphically to genuine automorphisms of the SAME
raw-coloured cover. Every E and P_c predicate is preserved.

This proves the unprescribed geometric group-action part of the
manuscript's fixed-cover lemma. It is not a coherent EPPA theorem:
preservation of an old nonempty embedded raw subset, individual
partial automorphism connectors and the groupoid assembly require
separate arguments.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {C : Type w}
variable {L : Type t} [AddCommGroup L] {V : Type z}
variable {d : RawDatum G C}

/-- Any reversal-safe H-action on a finite effective geometry lifts
homomorphically to ONE finite literal raw-fibre cover, without
requiring old prescribed points. The raw cover and its baseline
are chosen before specifying an element of H. -/
theorem exists_safeGroupRawCoverAction
    [Finite V] [Finite L]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (rho : H →* Equiv.Perm V)
    (hE : ∀ h : H, ∀ x y,
      D.part (rho h x) (rho h y) ↔ D.part x y)
    (hF : ∀ h : H, ∀ x y, ¬D.part x y →
      D.F (rho h x) (rho h y) = D.F x y)
    (hSafe : ∀ (h : H) (x y : V),
      ¬D.part x y →
      rho h x = y → rho h y = x →
      ∃ c : C, d.phi c = D.F x y ∧ d.reverse c = c) :
    Finite (RawCoverVertex V L) ∧
    ∃ (b : V → V → L)
      (hb : ∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y)
      (lift : H →* Equiv.Perm (RawCoverVertex V L)),
      (∀ (h : H) (X Y : RawCoverVertex V L),
        D.part (lift h X).1 (lift h Y).1 ↔
          D.part X.1 Y.1) ∧
      (∀ (h : H) (c : C) (X Y : RawCoverVertex V L),
        rawRel (rawCoverPresentation D code b hb).toStructure c
          (lift h X) (lift h Y) ↔
        rawRel (rawCoverPresentation D code b hb).toStructure c X Y) := by
  classical
  obtain ⟨b, _, hb⟩ :=
    exists_finiteResidualBaseline D code.shift code.shift_reverse
  obtain ⟨colour, hphi, hreverse, hInvariant⟩ :=
    exists_groupInvariantRawCrossColour D rho hE hF hSafe
  obtain ⟨r, hr, hR, hOld⟩ :=
    exists_codeInvariantResidualMatrix
      D code rho colour hphi hreverse hInvariant
      (∅ : Set V) b (by
        intro x y hx
        exact False.elim hx)
  have hS : ∀ h : H, ∀ x : V,
      x ∈ (∅ : Set V) → rho h x ∈ (∅ : Set V) := by
    intro h x hx
    exact False.elim hx
  obtain ⟨hFinite, nu, lift, hZero, hRec, hExt, hPart, hColour⟩ :=
    exists_fixedRawCoverGroupLift
      D code b r (∅ : Set V) hb hr hOld
      rho hE hF hR hS
  exact ⟨hFinite, b, hb, lift, hPart, hColour⟩

end SemigenericEPPA
