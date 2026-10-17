import SemigenericEPPA.Algebra.Gauge
import Mathlib.Tactic.Group

/-!
# Multiplier equations for effective EPPA witness automorphisms

The effective witness automorphisms act on gauge coordinates by
left multiplication. Given the original skeleton K=K(q,r),
the relabelled skeleton K'=K(σq,σr), and an arbitrarily chosen
multiplier m=m(q,r), equation (3.9) uniquely forces the reverse
multiplier n=m(r,q):

  t⁻¹*s(m)*(K')⁻¹*n = K⁻¹,
  n = K' * (t⁻¹*s(m))⁻¹ * K⁻¹,
  t = s(1).

Crucially, the *reverse ordered pair* also obeys equation (3.9)
with skeletons s(K),s(K'). This is not automatic for a generic
directed colouring and must be proved using the AFFINE involution,
including its nontrivial t-factor.

The final lemma proves the corresponding gauge-colour invariance
for all noncommutative group values. No finiteness or EPPA-existence
theorem is assumed.
-/

namespace SemigenericEPPA

universe u

variable {G : Type u} [Group G]

namespace AffineAntiInvolution

/-- Normalization of the affine reversal preserves inverses. -/
theorem normalized_inv (s : AffineAntiInvolution G) (x : G) :
    s.normalized x⁻¹ = (s.normalized x)⁻¹ := by
  unfold normalized
  rw [s.reverse_inv_affine]
  group

/-- Applying the normalized anti-involution twice gives conjugation
by the affine shift t=s(1), as required by the reverse (3.9) check. -/
theorem normalized_twice (s : AffineAntiInvolution G) (x : G) :
    s.normalized (s.normalized x) = (s 1)⁻¹ * x * s 1 := by
  unfold normalized
  rw [s.map_mul, s.reverse_inv_affine, s.involutive 1,
    s.involutive x]
  group

end AffineAntiInvolution

/-- The reverse ordered multiplier forced by equation (3.9),
using the true affine normalization t⁻¹ s(m). -/
def eppeReverseMultiplier (s : AffineAntiInvolution G)
    (K K' m : G) : G :=
  K' * (s.normalized m)⁻¹ * K⁻¹

/-- The forward ordered multiplier equation (3.9) holds by
construction, with the exact noncommutative factor order. -/
theorem eppe_reverseMultiplier_forward
    (s : AffineAntiInvolution G) (K K' m : G) :
    s.normalized m * (K')⁻¹ *
      eppeReverseMultiplier s K K' m = K⁻¹ := by
  unfold eppeReverseMultiplier
  group

/-- The reverse ordered multiplier is uniquely determined by the
forward equation, even without any finite-group assumption. -/
theorem eppe_reverseMultiplier_unique
    (s : AffineAntiInvolution G) (K K' m n : G)
    (h : s.normalized m * (K')⁻¹ * n = K⁻¹) :
    n = eppeReverseMultiplier s K K' m := by
  unfold eppeReverseMultiplier
  calc
    n = (s.normalized m * (K')⁻¹)⁻¹ *
        (s.normalized m * (K')⁻¹ * n) := by group
    _ = (s.normalized m * (K')⁻¹)⁻¹ * K⁻¹ := by rw [h]
    _ = K' * (s.normalized m)⁻¹ * K⁻¹ := by group

/-- Reverse ordered skeletons are s(K),s(K'). The same two
multipliers satisfy their OTHER orientation equation (3.9).
This is the genuinely affine/noncommutative part of the proof. -/
theorem eppe_reverseMultiplier_backward
    (s : AffineAntiInvolution G) (K K' m : G) :
    s.normalized (eppeReverseMultiplier s K K' m) *
        (s K')⁻¹ * m = (s K)⁻¹ := by
  have hnorm :
      s.normalized (eppeReverseMultiplier s K K' m) =
        (s.normalized K)⁻¹ *
          (s.normalized (s.normalized m))⁻¹ *
          s.normalized K' := by
    unfold eppeReverseMultiplier
    rw [s.normalized_mul, s.normalized_mul,
      s.normalized_inv, s.normalized_inv]
  rw [hnorm, s.normalized_twice]
  unfold AffineAntiInvolution.normalized
  group

/-- Equation (3.9) makes multiplying vertex valuations preserve the
effective cross colour F(X,Y) from equation (3.6). -/
theorem eppe_multiplier_preserves_gaugeColour
    (s : AffineAntiInvolution G)
    (K K' m n a b : G)
    (h : s.normalized m * (K')⁻¹ * n = K⁻¹) :
    gaugeColour s (m * a) K' (n * b) =
      gaugeColour s a K b := by
  unfold gaugeColour
  rw [s.map_mul]
  calc
    (s a * (s 1)⁻¹ * s m) * (K')⁻¹ * (n * b) =
        s a * (s.normalized m * (K')⁻¹ * n) * b := by
          unfold AffineAntiInvolution.normalized
          group
    _ = s a * K⁻¹ * b := by rw [h]

/-- Combining both orientations with gauge invariance: choosing
one ordered multiplier and computing its reverse always preserves
the effective group colour, without solving another independent
equation for the opposite orientation. -/
theorem eppe_forced_pair_preserves_colour
    (s : AffineAntiInvolution G) (K K' m a b : G) :
    gaugeColour s (m * a) K'
      (eppeReverseMultiplier s K K' m * b) =
        gaugeColour s a K b :=
  eppe_multiplier_preserves_gaugeColour
    s K K' m (eppeReverseMultiplier s K K' m) a b
    (eppe_reverseMultiplier_forward s K K' m)

end SemigenericEPPA
