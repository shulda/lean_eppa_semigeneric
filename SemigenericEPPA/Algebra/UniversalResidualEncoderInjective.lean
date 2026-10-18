import SemigenericEPPA.Algebra.UniversalResidualEncoder

/-!
# Faithfulness of the universal affine raw encoder

The first ZMod 4 vector coordinate of the explicit encoding already
distinguishes every raw colour, even across different effective fibres.
At the coordinate indexed by c itself the encoded vector has value

  2 if c*=c, and 1 otherwise.

At the coordinate c, the encoded vector of any *other* raw colour d
has value 0 or -1. These sets of values are disjoint in ZMod 4.
This gives an injective encoding without any cardinality argument.

Injectivity plus the previously checked affine equivariance makes the
encoder a genuinely equivariant embedding of raw reversal sets into
the universal finite residual coefficient group. A decoder is a
separate construction.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable [LinearOrder C]

/-- Evaluate the first coordinate of the code of c at c itself. -/
theorem universalResidualEncode_self
    (d : RawDatum G C) (c : C) :
    (universalResidualEncode d c).1 c =
      if d.reverse c = c then (2 : ZMod 4) else 1 := by
  classical
  by_cases hc : d.reverse c = c
  · simp [universalResidualEncode, hc,
      universalResidualFixedBasis]
  · have hcr : c ≠ d.reverse c := Ne.symm hc
    simp [universalResidualEncode, hc,
      universalResidualPairedBasis, universalResidualBasis, hcr]

/-- The same coordinate in the code of another raw colour
has value either 0 or -1 (modulo 4), depending on whether
c is the reversal of that other colour. -/
theorem universalResidualEncode_other
    (d : RawDatum G C) (c k : C) (hck : c ≠ k) :
    (universalResidualEncode d k).1 c =
      if d.reverse k = c then -(1 : ZMod 4) else 0 := by
  classical
  have hkc : k ≠ c := Ne.symm hck
  by_cases hk : d.reverse k = k
  · have hr : d.reverse k ≠ c := by
      rw [hk]
      exact hkc
    simp [universalResidualEncode, hk,
      universalResidualFixedBasis, hck, hkc, hr]
  · by_cases hr : d.reverse k = c
    · simp [universalResidualEncode, hk,
        universalResidualPairedBasis, universalResidualBasis,
        hkc, hr]
    · have hrc : c ≠ d.reverse k := Ne.symm hr
      simp [universalResidualEncode, hk,
        universalResidualPairedBasis, universalResidualBasis,
        hck, hkc, hr, hrc]

/-- The concrete universal encoder is injective on ALL raw colours,
not merely within one fixed fibre of phi. Its equivariance with
reversal is the preceding theorem in UniversalResidualEncoder. -/
theorem universalResidualEncode_injective
    (d : RawDatum G C) :
    Function.Injective (universalResidualEncode d) := by
  intro c k h
  by_contra hck
  have hval := congrArg
    (fun q : UniversalResidualCarrier C => q.1 c) h
  rw [universalResidualEncode_self d c,
    universalResidualEncode_other d c k hck] at hval
  have hsep :
      ∀ u v : ZMod 4,
        (u = 1 ∨ u = 2) →
        (v = 0 ∨ v = -1) → u ≠ v := by
    decide
  have hu :
      (if d.reverse c = c then (2 : ZMod 4) else 1) = 1 ∨
      (if d.reverse c = c then (2 : ZMod 4) else 1) = 2 := by
    split_ifs <;> simp
  have hv :
      (if d.reverse k = c then -(1 : ZMod 4) else 0) = 0 ∨
      (if d.reverse k = c then -(1 : ZMod 4) else 0) = -1 := by
    split_ifs <;> simp
  exact hsep _ _ hu hv hval

end SemigenericEPPA
