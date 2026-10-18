import SemigenericEPPA.Algebra.UniversalResidualCarrier

/-!
# An explicit equivariant raw-colour encoder into one universal group

For ANY raw datum, the group L_C=(C→ZMod 4)×ZMod 2 from the previous
module admits a direct raw-colour encoding:

* if c is reversal-fixed, encode it by (2 delta_c,0);
* otherwise encode it by the signed vector
  (delta_c-delta_(c*), epsilon_c).

The epsilon coordinate is t(phi c) if c*<c and zero otherwise,
where t is our universal affine shift. This orients each raw
two-cycle. It is automatically zero whenever the effective colour
has a reversal-fixed raw fibre point; in a fibre with no fixed
raw colour, reversal toggles the ZMod2 coordinate.

We verify the **exact** equivariance identity
  encode(c*) = t(phi c) - encode(c),
including the genuinely affine and non-self-reversing cases.

The next R0 gate will prove injectivity on each fibre and construct
an equivariant decoder/section using finite orbit representatives;
the encoder alone is not yet a full residual code.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}

/-- Universal explicit raw-colour encoder, with the affine shift
nonzero precisely on raw-fixed-point-free s-fixed effective fibres. -/
noncomputable def universalResidualEncode
    [LinearOrder C]
    (d : RawDatum G C) (c : C) :
    UniversalResidualCarrier C := by
  classical
  exact if d.reverse c = c then
    (universalResidualFixedBasis c, 0)
  else
    (universalResidualPairedBasis d c,
      if d.reverse c < c then (universalResidualShift d (d.phi c)).2
      else 0)

/-- Reversing the raw input keeps the chosen affine shift because
the effective image reverses by s. -/
theorem universalResidualEncode_shift_reverse
    (d : RawDatum G C) (c : C) :
    universalResidualShift d (d.phi (d.reverse c)) =
      universalResidualShift d (d.phi c) := by
  rw [d.equivariant]
  exact universalResidualShift_reverse d (d.phi c)

/-- Equation (3.20) for the universal encoder: arbitrary raw
reversal is represented by the AFFINE map z↦t(g)−z.
In particular, no involutivity assumption on g itself is used. -/
theorem universalResidualEncode_reverse
    [LinearOrder C]
    (d : RawDatum G C) (c : C) :
    universalResidualEncode d (d.reverse c) =
      universalResidualShift d (d.phi c) -
        universalResidualEncode d c := by
  classical
  by_cases hc : d.reverse c = c
  · have hfixed : d.phi c ∈ d.selfReverseEffective :=
      ⟨c, rfl, hc⟩
    have hshift := universalResidualShift_withFixedColour
      d (d.phi c) hfixed
    rw [hc, hshift]
    have henc : universalResidualEncode d c =
        (universalResidualFixedBasis c, (0 : ZMod 2)) := by
      simp [universalResidualEncode, hc]
    rw [henc]
    apply Prod.ext
    · change universalResidualFixedBasis c =
        (0 : C → ZMod 4) - universalResidualFixedBasis c
      rw [sub_eq_add_neg, zero_add, universalResidualFixedBasis_neg]
    · simp
  · have hrev : d.reverse (d.reverse c) ≠ d.reverse c := by
      simpa only [d.reverse_involutive] using hc.symm
    have hfirst : universalResidualEncode d c =
        (universalResidualPairedBasis d c,
          if d.reverse c < c then
            (universalResidualShift d (d.phi c)).2 else 0) := by
      simp [universalResidualEncode, hc]
    have hsecond :
        universalResidualEncode d (d.reverse c) =
          (universalResidualPairedBasis d (d.reverse c),
            if c < d.reverse c then
              (universalResidualShift d (d.phi (d.reverse c))).2
            else 0) := by
      simp [universalResidualEncode, hrev, d.reverse_involutive]
    rw [hfirst, hsecond, universalResidualEncode_shift_reverse d c]
    apply Prod.ext
    · change universalResidualPairedBasis d (d.reverse c) =
        (0 : C → ZMod 4) - universalResidualPairedBasis d c
      rw [universalResidualPairedBasis_reverse]
      simp
    · change
        (if c < d.reverse c then
          (universalResidualShift d (d.phi c)).2 else 0) =
        (universalResidualShift d (d.phi c)).2 -
          (if d.reverse c < c then
            (universalResidualShift d (d.phi c)).2 else 0)
      rcases lt_or_gt_of_ne hc.symm with hlt | hgt
      · have hnlt : ¬d.reverse c < c :=
          not_lt_of_ge (le_of_lt hlt)
        simp [hlt, hnlt]
      · have hnlt : ¬c < d.reverse c :=
          not_lt_of_ge (le_of_lt hgt)
        simp [hgt, hnlt]

end SemigenericEPPA
