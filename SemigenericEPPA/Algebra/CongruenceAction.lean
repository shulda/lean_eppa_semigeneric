import SemigenericEPPA.Algebra.Recenter
import SemigenericEPPA.Algebra.Gauge
import SemigenericEPPA.Algebra.RawDatum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Group

/-!
# Congruence action on fixed effective colours

For t = s(1) and α(a) = t⁻¹ * s(a), the affine congruence formula is
  a ⋆ g = a * g * α(a).
The s-fixed effective colours form a genuine G-set under this formula.

This is the precise orbit relation needed by the positive/negative coherent
and dense locally finite criteria.  We intentionally distinguish an
S-invariant set (all orbits good) from existence of one complete orbit.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G]

/-- Affine involution applied to its own normalized anti-automorphism. -/
theorem AffineAntiInvolution.reverse_normalized
    (s : AffineAntiInvolution G) (a : G) :
    s (s.normalized a) = a * s 1 := by
  change s ((s 1)⁻¹ * s a) = a * s 1
  rw [s.map_mul, s.involutive a, s.reverse_inv_affine (s 1), s.involutive 1]
  group

/-- The affine congruence action preserves exactly the fixed locus of
the original affine involution, without assuming s(1)=1. -/
theorem congruence_preserves_fixed
    (s : AffineAntiInvolution G) {g : G}
    (hg : s g = g) (a : G) :
    s (congruence s a g) = congruence s a g := by
  unfold congruence
  rw [s.map_mul, s.map_mul, s.reverse_normalized, hg]
  unfold AffineAntiInvolution.normalized
  group

/-- Effective colours that are fixed under the raw reversal's shadow. -/
abbrev ReversalFixed (s : AffineAntiInvolution G) : Type u :=
  { g : G // s g = g }

/-- The genuine left G-action on the fixed locus of an affine
anti-involution, even when its affine shift s(1) is nontrivial. -/
instance (s : AffineAntiInvolution G) : MulAction G (ReversalFixed s) where
  smul a g :=
    ⟨congruence s a g.1, congruence_preserves_fixed s g.2 a⟩
  one_smul := by
    intro g
    apply Subtype.ext
    change congruence s 1 g.1 = g.1
    exact congruence_one s g.1
  mul_smul := by
    intro a b g
    apply Subtype.ext
    change congruence s (a * b) g.1 =
      congruence s a (congruence s b g.1)
    exact congruence_mul s a b g.1

/-- Global orbit saturation, the positive coherent-EPPA hypothesis. -/
def CongruenceSaturated (s : AffineAntiInvolution G) (S : Set G) : Prop :=
  ∀ a g, g ∈ S → congruence s a g ∈ S

/-- One full congruence orbit contained in S, the weaker DLF hypothesis. -/
def ContainsCompleteCongruenceOrbit
    (s : AffineAntiInvolution G) (S : Set G) : Prop :=
  ∃ g, g ∈ S ∧ ∀ a, congruence s a g ∈ S

theorem containsCompleteOrbit_of_saturated
    (s : AffineAntiInvolution G) (S : Set G)
    (hs : CongruenceSaturated s S) (hne : S.Nonempty) :
    ContainsCompleteCongruenceOrbit s S := by
  obtain ⟨g, hg⟩ := hne
  exact ⟨g, hg, fun a => hs a g hg⟩

namespace RawDatum

variable {C : Type v}

/-- Saturation of the self-reversing effective-colour set S. -/
def IsCongruenceSaturated (d : RawDatum G C) : Prop :=
  CongruenceSaturated d.s d.selfReverseEffective

/-- Existence of a complete congruence orbit of self-reversing effective
colours; a priori weaker than global saturation. -/
def HasCompleteGoodOrbit (d : RawDatum G C) : Prop :=
  ContainsCompleteCongruenceOrbit d.s d.selfReverseEffective

theorem hasCompleteGoodOrbit_of_saturated
    (d : RawDatum G C)
    (hs : d.IsCongruenceSaturated)
    (hne : d.selfReverseEffective.Nonempty) :
    d.HasCompleteGoodOrbit :=
  containsCompleteOrbit_of_saturated d.s d.selfReverseEffective hs hne

end RawDatum

end SemigenericEPPA
