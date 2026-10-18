import SemigenericEPPA.Algebra.AffineResidualCode
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# A uniform finite coefficient group for every raw residual fibre

The existing affine residual-code interface uses a single additive
group L for all effective colours. An explicit common candidate,
depending only on the finite raw alphabet C, is

             L_C = (C -> ZMod 4) × ZMod 2.

The first factor has enough 2-torsion fixed points to encode arbitrary
self-reversing raw colours and enough order-four elements to encode
reversal pairs. The second factor supplies a fixed-point-free affine
reversal whenever an s-fixed effective fibre has NO self-reversing
raw colour.

For effective g, take the affine shift t(g)=(0,1) exactly if
s(g)=g and the raw fibre over g has no reversal-fixed colour,
and t(g)=0 otherwise. Then t(s(g))=t(g). This choice depends only
on the effective colour and not on any old structure.

This file establishes the carrier, universal shift, and
basis-vector reversal algebra. The next coding step is to construct
equivariant encoders/decoders and hence the actual AffineResidualCode
for every finite raw datum, without a per-orbit group product.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {C : Type v}

/-- A universal finite abelian scratch group for raw fibre coding.
The ZMod 2 coordinate permits free affine reversal; the vector
of ZMod 4 coordinates permits both fixed and paired orbits. -/
abbrev UniversalResidualCarrier (C : Type v) :=
  (C → ZMod 4) × ZMod 2

/-- Basis vector with coefficient 1 at raw colour c. -/
noncomputable def universalResidualBasis (c : C) : C → ZMod 4 := by
  classical
  exact fun x => if x = c then 1 else 0

/-- Basis vector with coefficient 2 at c, fixed by negation in ZMod 4. -/
noncomputable def universalResidualFixedBasis (c : C) : C → ZMod 4 := by
  classical
  exact fun x => if x = c then 2 else 0

/-- A signed basis vector for the reversal pair {c,c*}. -/
noncomputable def universalResidualPairedBasis
    (d : RawDatum G C) (c : C) : C → ZMod 4 :=
  universalResidualBasis c - universalResidualBasis (d.reverse c)

/-- The coefficient-2 basis is fixed by additive inversion. -/
theorem universalResidualFixedBasis_neg (c : C) :
    -universalResidualFixedBasis c = universalResidualFixedBasis c := by
  classical
  funext x
  by_cases hx : x = c
  · simp [universalResidualFixedBasis, hx] <;> decide
  · simp [universalResidualFixedBasis, hx]

/-- Reversal of a raw colour negates its signed paired basis, using
only the actual involution on raw colours. -/
theorem universalResidualPairedBasis_reverse
    (d : RawDatum G C) (c : C) :
    universalResidualPairedBasis d (d.reverse c) =
      -universalResidualPairedBasis d c := by
  funext x
  simp only [universalResidualPairedBasis, Pi.sub_apply,
    Pi.neg_apply, d.reverse_involutive]
  abel

/-- The universal affine shift is nonzero only over a fixed
effective colour whose raw fibre has NO fixed raw colour. -/
noncomputable def universalResidualShift
    (d : RawDatum G C) (g : G) : UniversalResidualCarrier C := by
  classical
  exact if d.s g = g ∧ g ∉ d.selfReverseEffective
    then (0, 1) else (0, 0)

/-- No affine shift is needed between a pair of distinct effective
colours, because raw reversal transfers the two fibres. -/
theorem universalResidualShift_nonfixed
    (d : RawDatum G C) (g : G) (hg : d.s g ≠ g) :
    universalResidualShift d g = 0 := by
  classical
  simp [universalResidualShift, hg]

/-- A self-reversing raw colour permits an affine reversal with a
fixed point, so our universal shift vanishes on that fibre. -/
theorem universalResidualShift_withFixedColour
    (d : RawDatum G C) (g : G)
    (hg : g ∈ d.selfReverseEffective) :
    universalResidualShift d g = 0 := by
  classical
  simp [universalResidualShift, hg]

/-- The affine shift is constant on each effective reversal orbit.
No assumption s(1)=1, commutativity of G, or saturation of S. -/
theorem universalResidualShift_reverse
    (d : RawDatum G C) (g : G) :
    universalResidualShift d (d.s g) =
      universalResidualShift d g := by
  classical
  by_cases hfix : d.s g = g
  · rw [hfix]
  · have hfix' : ¬ d.s (d.s g) = d.s g := by
      intro h
      apply hfix
      exact ((d.s.involutive g).symm.trans h).symm
    simp [universalResidualShift, hfix, hfix']

/-- If an effective colour is fixed by s but its raw fibre has no
self-reversing raw colour, affine reversal of the universal residual
carrier is FIXED-POINT-FREE. The extra ZMod 2 coordinate is essential:
negation alone would always fix the zero vector. -/
theorem universalResidualShift_free
    (d : RawDatum G C) (g : G)
    (hg : d.s g = g)
    (hS : g ∉ d.selfReverseEffective)
    (z : UniversalResidualCarrier C) :
    universalResidualShift d g - z ≠ z := by
  classical
  intro h
  have hshift :
      universalResidualShift d g =
        ((0 : C → ZMod 4), (1 : ZMod 2)) := by
    simp [universalResidualShift, hg, hS]
  have hsec := congrArg
    (fun q : UniversalResidualCarrier C => q.2) h
  rw [hshift] at hsec
  change (1 : ZMod 2) - z.2 = z.2 at hsec
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  have hbad : (1 : ZMod 2) = 0 := by
    calc
      1 = (1 - z.2) + z.2 := by abel
      _ = z.2 + z.2 :=
        congrArg (fun q : ZMod 2 => q + z.2) hsec
      _ = (2 : ZMod 2) * z.2 := by ring
      _ = 0 := by rw [htwo]; simp
  exact hone hbad

/-- The coefficient carrier is finite whenever C is finite,
including the empty alphabet as an abstract edge case. -/
theorem finite_universalResidualCarrier [Finite C] :
    Finite (UniversalResidualCarrier C) := by
  classical
  letI : Fintype C := Fintype.ofFinite _
  infer_instance

end SemigenericEPPA
