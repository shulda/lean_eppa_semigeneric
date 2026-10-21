import SemigenericEPPA.Structure.IndexedGauge
import Mathlib.Tactic.Group

/-!
# Gauge normal form with one constant reversal-fixed skeleton

The ordinary quotient-indexed gauge of an E-rectangle structure has
a generally nonconstant skeleton K(i,j). For the coherent-positive
simultaneous finite-group construction, a constant reversal-fixed
skeleton is substantially more convenient: it is invariant under ALL
permutations of old E-indices, including those supported on an induced
subset, regardless of the colours of outside-old-part edges.

We show that no effective rectangle data are lost: given ANY
reversal-fixed effective colour g0, apply the following explicit
pair-by-pair gauge recoding, using one arbitrary linear order on the
part indices:
  a'(x,j) = a(x,j)                                 if [x] <= j,
  a'(x,j) = g0 * K(j,[x])^(-1) * a(x,j)             if j < [x].
Replace every skeleton entry by g0.

For [x]=i<[y]=j, its two coordinates transform asymmetrically,
  a'(x,j)=a(x,j),  a'(y,i)=g0*K(i,j)^(-1)*a(y,i).
The new effective colour therefore is exactly the original
  s(a(x,j)) * K(i,j)^(-1) * a(y,i).
The opposite orientation follows from affine reversal, valid in
arbitrary nonabelian G with arbitrary s(1). No normalization of
s(1), cohomological triviality, or old colour saturation is assumed.

This proves the constant-skeleton effective representation required
for choosing one pre-H witness geometry in the nontrivial-G coherent
proof. It does not yet provide the old H-action or the raw lift.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {V : Type v} {I : Type w}
variable {s : AffineAntiInvolution G}

/-- A fixed constant-skeleton reparametrization of the SAME vertex
and E-part data. On each unordered pair i<j, all the gauge
correction is placed on the j-to-i coordinate. -/
def IndexedGauge.constantSkeletonGauge
    (P : IndexedGauge s V I) [LinearOrder I]
    (g0 : G) (hfixed : s g0 = g0) :
    IndexedGauge s V I where
  label := P.label
  skeleton := fun _ _ => g0
  skeleton_reverse := by
    intro i j _
    exact hfixed.symm
  vertexGauge := fun x j =>
    if j < P.label x then
      g0 * (P.skeleton j (P.label x))⁻¹ * P.vertexGauge x j
    else P.vertexGauge x j

/-- Formula on a positively ordered pair of genuinely different
old E-parts. No commutation or simplification of s(1) occurs. -/
theorem IndexedGauge.constantSkeletonGauge_cross_lt
    (P : IndexedGauge s V I) [LinearOrder I]
    (g0 : G) (hfixed : s g0 = g0)
    (x y : V) (hxy : P.label x < P.label y) :
    (P.constantSkeletonGauge g0 hfixed).effective x y =
      P.effective x y := by
  have hne : P.label x ≠ P.label y := ne_of_lt hxy
  have hnot : ¬P.label y < P.label x :=
    not_lt_of_ge (le_of_lt hxy)
  rw [(P.constantSkeletonGauge g0 hfixed).effective_cross x y hne,
      P.effective_cross x y hne]
  change gaugeColour s
      (if P.label y < P.label x then
        g0 * (P.skeleton (P.label y) (P.label x))⁻¹ *
          P.vertexGauge x (P.label y)
       else P.vertexGauge x (P.label y))
      g0
      (if P.label x < P.label y then
        g0 * (P.skeleton (P.label x) (P.label y))⁻¹ *
          P.vertexGauge y (P.label x)
       else P.vertexGauge y (P.label x)) =
    gaugeColour s
      (P.vertexGauge x (P.label y))
      (P.skeleton (P.label x) (P.label y))
      (P.vertexGauge y (P.label x))
  rw [if_neg hnot, if_pos hxy]
  unfold gaugeColour
  group

/-- The constant skeleton preserves every ORIGINAL effective
cross-E group colour and both E-classes literally. The opposite
order case follows from the exact affine anti-involution reversal
of the old and new indexed gauge presentations. -/
theorem IndexedGauge.constantSkeletonGauge_cross
    (P : IndexedGauge s V I) [LinearOrder I]
    (g0 : G) (hfixed : s g0 = g0)
    (x y : V) (hxy : P.label x ≠ P.label y) :
    (P.constantSkeletonGauge g0 hfixed).effective x y =
      P.effective x y := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact P.constantSkeletonGauge_cross_lt g0 hfixed x y hlt
  · have hyx : P.label y ≠ P.label x := Ne.symm hxy
    calc
      (P.constantSkeletonGauge g0 hfixed).effective x y =
          s ((P.constantSkeletonGauge g0 hfixed).effective y x) :=
        (P.constantSkeletonGauge g0 hfixed).effective_reverse y x hyx
      _ = s (P.effective y x) := by
        rw [P.constantSkeletonGauge_cross_lt g0 hfixed y x hgt]
      _ = P.effective x y :=
        (P.effective_reverse y x hyx).symm

/-- On the resulting actual effective geometry, both the binary
E-predicate and every cross-E effective colour are unchanged.
Same-part dummy colours are immaterial to the rectangle class. -/
theorem IndexedGauge.constantSkeletonGauge_geometry
    (P : IndexedGauge s V I) [LinearOrder I]
    (g0 : G) (hfixed : s g0 = g0) :
    (∀ x y : V,
      (P.constantSkeletonGauge g0 hfixed).toEffectiveGeometry.part x y ↔
        P.toEffectiveGeometry.part x y) ∧
    (∀ x y : V, ¬P.toEffectiveGeometry.part x y →
      (P.constantSkeletonGauge g0 hfixed).toEffectiveGeometry.F x y =
        P.toEffectiveGeometry.F x y) := by
  constructor
  · intro x y
    rfl
  · intro x y hxy
    exact P.constantSkeletonGauge_cross g0 hfixed x y hxy

end SemigenericEPPA
