import SemigenericEPPA.Valuations.ReferenceWitnessActionBridge
import SemigenericEPPA.Valuations.OldVertexExtensionCriterion
import Mathlib.Tactic.Group

/-!
# Exact old-vertex extension with nontrivial reference twists

For the relative finite H-action needed in the coherent-positive
nontrivial-G proof, H acts only on an old induced subset S. An
extension to the artificial old-label carrier can be compatible with
the quotient permutation without preserving the entire old effective
colour matrix. Thus the z=1 full-old-action lift is insufficient.

Fix arbitrary old gauge rows a(x,j). On witness parts q=(i,f), use
the genuine reference coboundary L^h_(x,j) and the permutation
  sigma_h(j,f)=(h j, f'),   f'(h x)=L^h_(x,j) f(x).
Use canonical index multipliers M^h_(i,j) on second-sort incidences.

For x in the selected old subset S, suppose:
* the reference twist is 1 in the occupied source class [x] at ALL
  old real labels, so the neutral witness part containing x stays
  neutral;
* M^h_([x],j) a(x,j) =
      a(h x,h j) L^h_(x,j)
  for every target index j.

Then the actual whole-witness permutation maps the complete old
gauge-valued vertex X_x to X_(h x), including EVERY cross-incidence.
The order on the right is essential in noncommutative G.

This isolates the true relative old-extension gate. It does not
assume full H-invariance of the old geometry and does not yet
construct the special reference functions or the multipliers from S.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- The old copy with arbitrary supplied gauge row a, retaining the
same neutral part, genuine old real label, and independent incidence
towards each other witness part. It specializes to the canonical
quotient-gauge old embedding and to a recoded constant-skeleton copy. -/
noncomputable def gaugeOldWitnessVertex
    (D : EffectiveGeometry s V)
    (a : V → Quotient D.part → G) (x : V) :
    EffectiveWitnessVertex D where
  part := oldWitnessPart D x
  old := x
  belongs := rfl
  vertexValuation := fun r => a x r.1.1

/-- The extension datum M_h(i,j) is pulled back to all witness-part
pairs, while the first-sort permutation uses the noncommutative
reference-gauge coboundary. -/
noncomputable def referenceIndexedWitnessAction
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j) :
    H →* Equiv.Perm (EffectiveWitnessVertex D) :=
  referenceWitnessCocycleAction D rho iota z hcls
    (fun h q r => M h q.1 r.1)
    (by
      intro q r _
      exact hOne q.1 r.1)
    (by
      intro k h q r _
      change M (k * h) q.1 r.1 =
        M k
          (referenceWitnessPartAction D rho iota z h q).1
          (referenceWitnessPartAction D rho iota z h r).1 *
            M h q.1 r.1
      rw [referenceWitnessPartAction_class D rho iota z h q,
        referenceWitnessPartAction_class D rho iota z h r]
      exact hMul k h q.1 r.1)

/-- The actual group homomorphism of the whole valuation witness
extends a prescribed H-action on the selected OLD subset, under
precisely the old-row/reference-twist equations. In particular, no
H-automorphism assumption is made on all V, and we do not assert
that the selected subset is closed under its ambient E-classes. -/
theorem referenceIndexedWitnessAction_maps_gaugeOld_onSubset
    (D : EffectiveGeometry s V)
    (S : Set V)
    (a : V → Quotient D.part → G)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (hSource : ∀ (h : H) (x : V), x ∈ S →
      ∀ y : V,
        z (rho h y) (iota h (Quotient.mk D.part x)) =
          z y (Quotient.mk D.part x))
    (hRow : ∀ (h : H) (x : V), x ∈ S →
      ∀ j : Quotient D.part,
        M h (Quotient.mk D.part x) j * a x j =
          a (rho h x) (iota h j) *
            referenceGaugeTwist rho iota z h x j)
    (h : H) (x : V) (hx : x ∈ S) :
    D.referenceIndexedWitnessAction rho iota z hcls
        M hOne hMul h (D.gaugeOldWitnessVertex a x) =
      D.gaugeOldWitnessVertex a (rho h x) := by
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    referenceWitnessPartAction D rho iota z
  let m : H → EffectiveWitnessPart D → EffectiveWitnessPart D → G :=
    fun h q r => M h q.1 r.1
  let T : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.referenceIndexedWitnessAction rho iota z hcls M hOne hMul
  let X : EffectiveWitnessVertex D := D.gaugeOldWitnessVertex a x
  let Y : EffectiveWitnessVertex D := D.gaugeOldWitnessVertex a (rho h x)
  have hNeutral (j : Quotient D.part)
      (hj : j = Quotient.mk D.part x) :
      sigma h (distinguishedWitnessPart D j) =
        distinguishedWitnessPart D (iota h j) := by
    apply referenceWitnessPartAction_neutral D rho iota z h j
    intro y
    subst j
    exact hSource h x hx y
  have hSigmaVal (r : EffectiveWitnessPart D) :
      (sigma h r).2 (rho h x) =
        referenceGaugeTwist rho iota z h x r.1 * r.2 x := by
    change
      (twistedWitnessPartPerm D (iota h) (rho h)
        (fun j y => referenceGaugeTwist rho iota z h y j) r).2
          (rho h x) =
        referenceGaugeTwist rho iota z h x r.1 * r.2 x
    exact twistedWitnessPartPerm_valuation D
      (iota h) (rho h)
      (fun j y => referenceGaugeTwist rho iota z h y j) r x
  have hPart : (T h X).part = Y.part := by
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).part = Y.part
    rw [witnessCocyclePerm_part]
    change sigma h (oldWitnessPart D x) =
      oldWitnessPart D (rho h x)
    calc
      sigma h (oldWitnessPart D x) =
        distinguishedWitnessPart D (iota h (Quotient.mk D.part x)) :=
          hNeutral (Quotient.mk D.part x) rfl
      _ = oldWitnessPart D (rho h x) := by
        rw [← hcls h x]
        rfl
  have hOld : (T h X).old = Y.old := by
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).old = rho h x
    exact witnessCocyclePerm_old D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X
  apply EffectiveWitnessVertex.eq_of_crossIncidence (T h X) Y
    hPart hOld
  intro r hrT hrY
  let u : EffectiveWitnessPart D := (sigma h).symm r
  have hSigmaPart : (T h X).part = sigma h X.part := by
    change (witnessCocyclePerm D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X).part = sigma h X.part
    exact witnessCocyclePerm_part D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X
  have hu : u ≠ X.part := by
    intro heq
    apply hrT
    calc
      r = sigma h u := ((sigma h).apply_symm_apply r).symm
      _ = sigma h X.part := congrArg (sigma h) heq
      _ = (T h X).part := hSigmaPart.symm
  have hTransportNe : sigma h u ≠ (T h X).part := by
    intro heq
    apply hu
    apply (sigma h).injective
    calc
      sigma h u = (T h X).part := heq
      _ = sigma h X.part := hSigmaPart
  have hTargetNe : sigma h u ≠ Y.part := by
    intro heq
    apply hu
    apply (sigma h).injective
    calc
      sigma h u = Y.part := heq
      _ = (T h X).part := hPart.symm
      _ = sigma h X.part := hSigmaPart
  have hTransport :
      (T h X).crossIncidence (sigma h u) hTransportNe =
        m h X.part u * X.crossIncidence u hu :=
    witnessCocyclePerm_incidence D sigma rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      m h X u hu
  have hTarget :
      Y.crossIncidence (sigma h u) hTargetNe =
        m h X.part u * X.crossIncidence u hu := by
    have hClass : (sigma h u).1 = iota h u.1 :=
      referenceWitnessPartAction_class D rho iota z h u
    change
      a (rho h x) (sigma h u).1 *
        (sigma h u).2 (rho h x) =
      M h (Quotient.mk D.part x) u.1 *
        (a x u.1 * u.2 x)
    rw [hClass, hSigmaVal]
    calc
      a (rho h x) (iota h u.1) *
          (referenceGaugeTwist rho iota z h x u.1 * u.2 x) =
        (a (rho h x) (iota h u.1) *
            referenceGaugeTwist rho iota z h x u.1) * u.2 x := by group
      _ = (M h (Quotient.mk D.part x) u.1 * a x u.1) * u.2 x := by
        rw [hRow h x hx u.1]
      _ = M h (Quotient.mk D.part x) u.1 *
          (a x u.1 * u.2 x) := by group
  have hresult := hTransport.trans hTarget.symm
  simpa only [u, Equiv.apply_symm_apply] using hresult

end EffectiveGeometry

end SemigenericEPPA
