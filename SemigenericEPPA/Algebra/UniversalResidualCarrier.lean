import SemigenericEPPA.Algebra.AffineResidualCode
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel

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
  · simp [universalResidualFixedBasis, hx]
    decide
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
      exact (d.s.involutive g).symm.trans h
    simp [universalResidualShift, hfix, hfix']

/-- The coefficient carrier is finite whenever C is finite,
including the empty alphabet as an abstract edge case. -/
theorem finite_universalResidualCarrier [Finite C] :
    Finite (UniversalResidualCarrier C) := by
  classical
  letI : Fintype C := Fintype.ofFinite _
  infer_instance

end SemigenericEPPA
