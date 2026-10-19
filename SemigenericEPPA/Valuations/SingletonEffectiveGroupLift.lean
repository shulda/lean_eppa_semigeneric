import SemigenericEPPA.Valuations.InvariantSkeletonGroupAction

/-!
# Strict finite-group lifts when the effective colour group is trivial

For the free effective sector G=1, every function V→G and every
witness incidence coordinate are uniquely determined. The effective
valuation witness has no gauge obstruction: any compatible actions
on real labels and old E-classes extend automatically to a genuine
group action on the WHOLE two-layer witness which carries each
distinguished old vertex to its prescribed image.

We do not choose an H-dependent witness or independently extend
each h. The action is a single homomorphism H→Perm(B), and is
an automorphism of the SAME witness skeleton for every h.

The remaining coherent EPPA step for G=1 is combinatorial:
construct compatible rho/iota actions for Aut(D) on the SAME
padded old carrier for every induced D⊆A, then assemble the
groupoid. No complete coherent-EPPA claim is made here.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {s : AffineAntiInvolution G}

/-- Any group action on the old E-class imaginary sort induces a
homomorphic action on witness parts by leaving their valuation
functions unchanged. No condition on G is needed here. -/
noncomputable def quotientIndexWitnessPartAction
    (D : EffectiveGeometry s V)
    (iota : H →* Equiv.Perm (Quotient D.part)) :
    H →* Equiv.Perm (EffectiveWitnessPart D) where
  toFun := fun h => {
    toFun := fun q => (iota h q.1, q.2)
    invFun := fun q => ((iota h).symm q.1, q.2)
    left_inv := by
      rintro ⟨j, f⟩
      apply Prod.ext
      · exact (iota h).symm_apply_apply j
      · rfl
    right_inv := by
      rintro ⟨j, f⟩
      apply Prod.ext
      · exact (iota h).apply_symm_apply j
      · rfl
  }
  map_one' := by
    apply Equiv.ext
    rintro ⟨j, f⟩
    change (iota (1 : H) j, f) = (j, f)
    simp
  map_mul' := by
    intro k h
    apply Equiv.ext
    rintro ⟨j, f⟩
    change (iota (k * h) j, f) =
      (iota k (iota h j), f)
    rw [map_mul]
    rfl

/-- Exact compatibility of the quotient-index part action with
the prescribed group action on actual real vertices. -/
theorem quotientIndexWitnessPartAction_fibre_compat
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (h : H) (q : EffectiveWitnessPart D) (x : V) :
    (Quotient.mk D.part (rho h x) =
        (quotientIndexWitnessPartAction D iota h q).1) ↔
      (Quotient.mk D.part x = q.1) := by
  change Quotient.mk D.part (rho h x) =
      iota h q.1 ↔ Quotient.mk D.part x = q.1
  rw [hcls h x]
  constructor
  · exact (iota h).injective
  · intro heq
    exact congrArg (iota h) heq

/-- Distinguished neutral parts are mapped to distinguished neutral
parts with the correct old class label, regardless of G. -/
theorem quotientIndexWitnessPartAction_oldPart
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (h : H) (x : V) :
    quotientIndexWitnessPartAction D iota h (oldWitnessPart D x) =
      oldWitnessPart D (rho h x) := by
  change (iota h (Quotient.mk D.part x),
      (neutralPartValuation : V → G)) =
    (Quotient.mk D.part (rho h x), neutralPartValuation)
  rw [hcls h x]

/-- For a singleton effective group, EVERY compatible action of H
on old real vertices and their E-classes has an explicit extension
to the full effective witness. This is one strict group
homomorphism, preserving E and F and acting on EVERY distinguished
old vertex exactly as rho.

The skeleton K is arbitrary and chosen BEFORE H. Its invariance
is automatic because all G-valued colours are equal. -/
theorem exists_subsingletonEffectiveWitnessGroupLift
    [Subsingleton G]
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x)) :
    ∃ T : H →* Equiv.Perm (EffectiveWitnessVertex D),
      (∀ (h : H) (x : V),
        T h (D.oldWitnessVertex x) =
          D.oldWitnessVertex (rho h x)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        K.toEffectiveGeometry.part (T h X) (T h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D),
        ¬K.toEffectiveGeometry.part X Y →
          K.toEffectiveGeometry.F (T h X) (T h Y) =
            K.toEffectiveGeometry.F X Y) := by
  let sigma : H →* Equiv.Perm (EffectiveWitnessPart D) :=
    quotientIndexWitnessPartAction D iota
  have hc : ∀ (h : H) (q : EffectiveWitnessPart D) (x : V),
      (Quotient.mk D.part (rho h x) = (sigma h q).1) ↔
        (Quotient.mk D.part x = q.1) :=
    quotientIndexWitnessPartAction_fibre_compat D rho iota hcls
  let T : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    invariantSkeletonWitnessAction D sigma rho hc
  refine ⟨T, ?_, ?_, ?_⟩
  · intro h x
    change witnessCocyclePerm D sigma rho hc
      (fun _ _ _ => (1 : G)) h (D.oldWitnessVertex x) =
        D.oldWitnessVertex (rho h x)
    apply EffectiveWitnessVertex.eq_of_crossIncidence
    · calc
        (witnessCocyclePerm D sigma rho hc
            (fun _ _ _ => (1 : G)) h
              (D.oldWitnessVertex x)).part =
          sigma h (oldWitnessPart D x) :=
            witnessCocyclePerm_part D sigma rho hc
              (fun _ _ _ => 1) h (D.oldWitnessVertex x)
        _ = oldWitnessPart D (rho h x) :=
          quotientIndexWitnessPartAction_oldPart D rho iota hcls h x
        _ = (D.oldWitnessVertex (rho h x)).part := rfl
    · calc
        (witnessCocyclePerm D sigma rho hc
            (fun _ _ _ => (1 : G)) h
              (D.oldWitnessVertex x)).old =
          rho h x := witnessCocyclePerm_old D sigma rho hc
            (fun _ _ _ => 1) h (D.oldWitnessVertex x)
        _ = (D.oldWitnessVertex (rho h x)).old := rfl
    · intro r hr₁ hr₂
      exact Subsingleton.elim _ _
  · intro h X Y
    exact (invariantSkeletonWitnessAction_subsingleton_effective
      D K sigma rho hc h).1 X Y
  · intro h X Y hXY
    exact (invariantSkeletonWitnessAction_subsingleton_effective
      D K sigma rho hc h).2 X Y hXY

end SemigenericEPPA
