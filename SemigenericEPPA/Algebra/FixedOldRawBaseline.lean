import SemigenericEPPA.Algebra.RelativeResidualBaseline
import SemigenericEPPA.Algebra.AffineResidualGlobalEncoder

/-!
# A raw baseline chosen BEFORE all subsequent finite-group actions

In the coherent-EPPA construction the raw cover must be independent
of the induced old substructure D and its automorphism group H.
Consequently its additive baseline b must be fixed once, from the
raw colours of the WHOLE old copy A, not separately for each H.

Given a finite effective geometry and an old vertex set S₀ with
prescribed literal raw colours on all old-old cross-E pairs, encode
those colours by the actual affine residual sections. These
references reverse correctly because both raw reversal and the
canonical global encoder commute with the affine involution.

Apply the certified relative-baseline theorem once to obtain b on
the entire effective carrier. Then its prescribed section identities
hold for EVERY later subset S ⊆ S₀, with no mention of the group H.

This is the quantifier order needed to reuse precisely the same
raw cover when lifting the different groups Aut(D) for D ⊆ A.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] {C : Type v}
variable {L : Type w} [AddCommGroup L]
variable {V : Type t} {d : RawDatum G C}

/-- Fix a single affine raw baseline from the prescribed raw
colouring of the entire old subset S₀. It is compatible with
every later S ⊆ S₀, regardless of its group action. -/
theorem exists_finiteBaseline_prescribingOldRawColours
    [Finite V]
    (D : EffectiveGeometry d.s V)
    (code : AffineResidualCode d L)
    (S₀ : Set V)
    (old : V → V → C)
    (hPhi : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y, x ∈ S₀ → y ∈ S₀ →
      ¬D.part x y → old y x = d.reverse (old x y)) :
    ∃ b : V → V → L,
      (∀ x y, ¬D.part x y →
        b y x = code.shift (D.F x y) - b x y) ∧
      (∀ (S : Set V), S ⊆ S₀ →
        ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
          b x y = code.encodeRaw (old x y)) := by
  classical
  let oldResidual : V → V → L :=
    fun x y => code.encodeRaw (old x y)
  have hOld :
      ∀ x y, x ∈ S₀ → y ∈ S₀ → ¬D.part x y →
        oldResidual y x =
          code.shift (D.F x y) - oldResidual x y := by
    intro x y hx hy hxy
    change code.encodeRaw (old y x) =
      code.shift (D.F x y) - code.encodeRaw (old x y)
    calc
      code.encodeRaw (old y x) =
          code.encodeRaw (d.reverse (old x y)) := by
            rw [hReverse x y hx hy hxy]
      _ = code.shift (d.phi (old x y)) -
          code.encodeRaw (old x y) :=
            code.encodeRaw_reverse (old x y)
      _ = code.shift (D.F x y) -
          code.encodeRaw (old x y) := by
            rw [hPhi x y hx hy hxy]
  obtain ⟨b, hb, hPrescribed⟩ :=
    exists_finiteResidualBaseline_extendingSubset
      D code.shift code.shift_reverse S₀ oldResidual hOld
  refine ⟨b, hb, ?_⟩
  intro S hS x y hx hy hxy
  exact hPrescribed x y (hS hx) (hS hy) hxy

end SemigenericEPPA
