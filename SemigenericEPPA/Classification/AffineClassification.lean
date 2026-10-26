import SemigenericEPPA.Classification.GroupRepresentation
import SemigenericEPPA.Algebra.RawDatum
import Mathlib.Tactic.Group

/-!
# The affine anti-involution reconstructed from starred transpose

A general rectangle rule satisfying row amalgamation and corner
completion reconstructs an actual RawDatum, including the noncommutative
affine anti-involution. No finite assumption is used until the final
finite-group conclusion.

The remaining structural task is to derive row amalgamation and corner
completion from literal SAP for the unrestricted rectangle age.
-/

namespace SemigenericEPPA.Classification

universe u

namespace RectangleRule

variable {C : Type u} (R : RectangleRule C)
variable (hrow : R.HasRowAmalgamation)
variable (hcorner : R.HasCornerCompletion)

/-- Starred transpose and corner completion force the *affine*
anti-multiplication law on the reconstructed group. Reversal need not
fix the identity. -/
theorem reconstructedReverse_mul
    (origin : C)
    (g h : R.ReconstructedGroup hrow hcorner) :
    R.reconstructedReverse hrow hcorner origin (g * h) =
      R.reconstructedReverse hrow hcorner origin h *
      (R.reconstructedReverse hrow hcorner origin 1)⁻¹ *
      R.reconstructedReverse hrow hcorner origin g := by
  obtain ⟨a, rfl⟩ :=
    R.reconstructedPhi_surjective hrow hcorner origin g
  obtain ⟨b, rfl⟩ :=
    R.reconstructedPhi_surjective hrow hcorner origin h
  let phi := R.reconstructedPhi hrow hcorner origin
  let s := R.reconstructedReverse hrow hcorner origin
  obtain ⟨d, hd⟩ := hcorner origin b a
  have hp : (phi origin)⁻¹ * phi b = (phi a)⁻¹ * phi d :=
    (R.allowed_iff_reconstructed_difference
      hrow hcorner origin origin b a d).mp hd
  have hp' : phi b = (phi a)⁻¹ * phi d := by
    simpa only [phi, R.reconstructedPhi_origin_one hrow hcorner origin,
      one_inv, one_mul] using hp
  have hprod : phi d = phi a * phi b := by
    calc
      phi d = phi a * ((phi a)⁻¹ * phi d) := by group
      _ = phi a * phi b := by rw [← hp']
  have htranspose :
      R.allowed (R.reverse origin) (R.reverse a)
        (R.reverse b) (R.reverse d) :=
    (R.starred_transpose origin b a d).mp hd
  have hs :
      (phi (R.reverse origin))⁻¹ * phi (R.reverse a) =
        (phi (R.reverse b))⁻¹ * phi (R.reverse d) :=
    (R.allowed_iff_reconstructed_difference hrow hcorner origin
      (R.reverse origin) (R.reverse a)
      (R.reverse b) (R.reverse d)).mp htranspose
  change (R.reconstructedPhi hrow hcorner origin (R.reverse origin))⁻¹ *
      R.reconstructedPhi hrow hcorner origin (R.reverse a) =
    (R.reconstructedPhi hrow hcorner origin (R.reverse b))⁻¹ *
      R.reconstructedPhi hrow hcorner origin (R.reverse d) at hs
  rw [R.reconstructedPhi_reverse hrow hcorner origin origin,
      R.reconstructedPhi_reverse hrow hcorner origin a,
      R.reconstructedPhi_reverse hrow hcorner origin b,
      R.reconstructedPhi_reverse hrow hcorner origin d,
      R.reconstructedPhi_origin_one hrow hcorner origin,
      hprod] at hs
  change (s 1)⁻¹ * s (phi a) =
    (s (phi b))⁻¹ * s (phi a * phi b) at hs
  change s (phi a * phi b) =
    s (phi b) * (s 1)⁻¹ * s (phi a)
  calc
    s (phi a * phi b) =
      s (phi b) * ((s (phi b))⁻¹ * s (phi a * phi b)) := by group
    _ = s (phi b) * ((s 1)⁻¹ * s (phi a)) := by rw [← hs]
    _ = s (phi b) * (s 1)⁻¹ * s (phi a) := by group

/-- An actual affine anti-involution on the reconstructed group. -/
noncomputable def reconstructedAffineAntiInvolution
    (origin : C) :
    AffineAntiInvolution (R.ReconstructedGroup hrow hcorner) where
  toFun := R.reconstructedReverse hrow hcorner origin
  involutive := R.reconstructedReverse_involutive hrow hcorner origin
  map_mul := R.reconstructedReverse_mul hrow hcorner origin

/-- The complete classified datum, with the original raw alphabet. -/
noncomputable def reconstructedRawDatum (origin : C) :
    RawDatum (R.ReconstructedGroup hrow hcorner) C where
  s := R.reconstructedAffineAntiInvolution hrow hcorner origin
  reverse := R.reverse
  reverse_involutive := R.reverse_involutive
  phi := R.reconstructedPhi hrow hcorner origin
  phi_surjective := R.reconstructedPhi_surjective hrow hcorner origin
  equivariant := R.reconstructedPhi_reverse hrow hcorner origin

/-- The reconstructed datum represents the *exact* original P, not
merely a strengthening or weakening of its rectangle constraints. -/
theorem allowed_iff_reconstructedRawDatum
    (origin a b c d : C) :
    R.allowed a b c d ↔
      ((R.reconstructedRawDatum hrow hcorner origin).phi a)⁻¹ *
        (R.reconstructedRawDatum hrow hcorner origin).phi b =
      ((R.reconstructedRawDatum hrow hcorner origin).phi c)⁻¹ *
        (R.reconstructedRawDatum hrow hcorner origin).phi d :=
  R.allowed_iff_reconstructed_difference hrow hcorner origin a b c d

/-- A finite raw alphabet gives a finite reconstructed group:
the raw-colour map is a genuine surjection. -/
theorem reconstructedGroup_finite
    [Finite C] (origin : C) :
    Finite (R.ReconstructedGroup hrow hcorner) :=
  Finite.of_surjective
    (R.reconstructedPhi hrow hcorner origin)
    (R.reconstructedPhi_surjective hrow hcorner origin)

end RectangleRule
end SemigenericEPPA.Classification
