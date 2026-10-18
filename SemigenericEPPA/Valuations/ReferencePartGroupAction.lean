import SemigenericEPPA.Algebra.EffectiveGroupGaugeCocycles
import SemigenericEPPA.Valuations.TwistedPartPermutation
import Mathlib.Tactic.Group

/-!
# Homomorphic action on the effective valuation-part sort (4.27–4.28)

The partial-automorphism construction has a permutation of witness
parts for any individual real-label permutation rho, class-index
permutation iota, and twists L_j(x). The coherent-positive argument
needs one group homomorphism H → Perm(witness parts), not unrelated
permutations for each h∈H.

Use the explicit reference-gauge twists
  L^h_(x,j) = z_(rho(h)x,iota(h)j)^(-1) * z_(x,j).
Their noncommutative cocycle law was verified in #150, so the
resulting permutations

  sigma_h(j,f) = (iota(h)j, f')
  f'(rho(h)x) = L^h_(x,j) * f(x)

compose exactly. This is the actual witness-part action, not only
an abstract cocycle equation. No finite-group, normality,
recentring, or raw-colour hypothesis is used.

A homomorphic action on the FULL two-layer effective witness
requires compatible pair multipliers and their own cocycle law;
neither is asserted in this module.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

/-- Part permutation from a global reference-gauge coboundary. -/
noncomputable def referenceWitnessPartPerm
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (h : H) : Equiv.Perm (EffectiveWitnessPart D) :=
  twistedWitnessPartPerm D (iota h) (rho h)
    (fun j x => referenceGaugeTwist rho iota z h x j)

/-- The witness-part action fixes the identity strictly. -/
theorem referenceWitnessPartPerm_one
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G) :
    referenceWitnessPartPerm D rho iota z 1 = 1 := by
  apply Equiv.ext
  intro q
  apply Prod.ext
  · change iota (1 : H) q.1 = q.1
    simp
  · funext x
    change (twistPartValuation (rho (1 : H))
      (fun y => referenceGaugeTwist rho iota z (1 : H) y q.1) q.2) x = q.2 x
    simp [twistPartValuation, referenceGaugeTwist_one]

/-- The witness-part action respects the FULL group product. The
order is sigma_(k*h) = sigma_k ∘ sigma_h, with the noncommutative
left twist multiplying on the left at the target coordinate. -/
theorem referenceWitnessPartPerm_mul_apply
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (k h : H) (q : EffectiveWitnessPart D) :
    referenceWitnessPartPerm D rho iota z (k * h) q =
      referenceWitnessPartPerm D rho iota z k
        (referenceWitnessPartPerm D rho iota z h q) := by
  apply Prod.ext
  · change iota (k * h) q.1 = iota k (iota h q.1)
    rw [map_mul]
    rfl
  · funext y
    let x : V := (rho (k * h)).symm y
    have hy : rho (k * h) x = y :=
      (rho (k * h)).apply_symm_apply y
    have hcomp : rho k (rho h x) = rho (k * h) x := by
      rw [map_mul]
      rfl
    calc
      (referenceWitnessPartPerm D rho iota z (k * h) q).2 y =
          referenceGaugeTwist rho iota z (k * h) x q.1 * q.2 x := by
            rw [← hy]
            exact twistedWitnessPartPerm_valuation D
              (iota (k * h)) (rho (k * h))
              (fun j v => referenceGaugeTwist rho iota z (k * h) v j)
              q x
      _ = referenceGaugeTwist rho iota z k (rho h x) (iota h q.1) *
            (referenceGaugeTwist rho iota z h x q.1 * q.2 x) := by
          rw [referenceGaugeTwist_mul]
          group
      _ = (referenceWitnessPartPerm D rho iota z k
            (referenceWitnessPartPerm D rho iota z h q)).2 y := by
          rw [← hy, ← hcomp]
          have houter := twistedWitnessPartPerm_valuation D
              (iota k) (rho k)
              (fun j v => referenceGaugeTwist rho iota z k v j)
              (referenceWitnessPartPerm D rho iota z h q)
              (rho h x)
          have hinner := twistedWitnessPartPerm_valuation D
              (iota h) (rho h)
              (fun j v => referenceGaugeTwist rho iota z h v j)
              q x
          calc
            referenceGaugeTwist rho iota z k (rho h x) (iota h q.1) *
                (referenceGaugeTwist rho iota z h x q.1 * q.2 x) =
              referenceGaugeTwist rho iota z k (rho h x) (iota h q.1) *
                ((referenceWitnessPartPerm D rho iota z h q).2 (rho h x)) := by
                  rw [hinner]
            _ = (referenceWitnessPartPerm D rho iota z k
                  (referenceWitnessPartPerm D rho iota z h q)).2
                  (rho k (rho h x)) := by
                    exact houter.symm

/-- The cocycle (4.27) gives an actual group homomorphism into
the entire witness-part permutation group, not just separate
permutations or their first quotient coordinates. -/
noncomputable def referenceWitnessPartAction
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G) :
    H →* Equiv.Perm (EffectiveWitnessPart D) where
  toFun := referenceWitnessPartPerm D rho iota z
  map_one' := referenceWitnessPartPerm_one D rho iota z
  map_mul' := by
    intro k h
    apply Equiv.ext
    intro q
    change referenceWitnessPartPerm D rho iota z (k * h) q =
      (referenceWitnessPartPerm D rho iota z k *
       referenceWitnessPartPerm D rho iota z h) q
    rw [Equiv.Perm.mul_apply]
    exact referenceWitnessPartPerm_mul_apply D rho iota z k h q

end SemigenericEPPA
