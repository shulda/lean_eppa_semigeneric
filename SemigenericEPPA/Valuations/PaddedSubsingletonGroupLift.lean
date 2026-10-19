import SemigenericEPPA.Valuations.SingletonEffectiveGroupLift
import SemigenericEPPA.Structure.PaddedQuotientEquiv

/-!
# A fixed padded witness admits relative group lifts when G is trivial

The ordinary effective EPPA proof pads V to (V/E) × V once, before any
later partial map.  In the trivial effective-colour group sector we can
do more: a homomorphic action on the real label V and on the old
E-class indices gives a genuine action on that SAME padded carrier.

The two actions need only agree on the chosen H-invariant old subset
S whose automorphism group is being lifted.  They need not preserve
the E-relation of the original V globally.  This distinction is crucial:
an occupied E-class can contain original vertices outside S.

Because the padded E-relation depends only on the first coordinate,
the product action always preserves the padded E-classes globally.
Conjugating the quotient action and applying the already certified
singleton-group valuation theorem yields one H-action on the ENTIRE
two-layer witness, preserving its effective E/F-structure, with exact
old-vertex equivariance over S.

This is a conditional relative group-lift theorem.  Producing the
two homomorphic actions for every S and assembling coherent partial
isomorphisms are separate obligations.
-/

namespace SemigenericEPPA

universe u v w

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] [Subsingleton G]
variable {V : Type w} {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- A relative strict group lift on ONE uniform padded effective witness.
The original padded geometry and its skeleton are fixed before H, S
and the actions are supplied.  Only their compatibility on S is
required; in particular rho need not preserve the original E-classes
of V away from S. -/
theorem exists_paddedSubsingletonWitnessGroupLift
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D.uniformPaddedGeometry)
    (S : Set V)
    (rho : H →* Equiv.Perm S)
    (tau : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (hTau : ∀ (h : H) (x : S),
      tau h x.val = (rho h x).val)
    (hIota : ∀ (h : H) (x : S),
      iota h (Quotient.mk D.part x.val) =
        Quotient.mk D.part (rho h x).val) :
    ∃ T : H →* Equiv.Perm
        (EffectiveWitnessVertex D.uniformPaddedGeometry),
      (∀ (h : H) (x : S),
        T h (D.uniformPaddedGeometry.oldWitnessVertex
          (D.paddedOldMap x.val)) =
          D.uniformPaddedGeometry.oldWitnessVertex
            (D.paddedOldMap (rho h x).val)) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D.uniformPaddedGeometry),
        K.toEffectiveGeometry.part (T h X) (T h Y) ↔
          K.toEffectiveGeometry.part X Y) ∧
      (∀ (h : H) (X Y : EffectiveWitnessVertex D.uniformPaddedGeometry),
        ¬K.toEffectiveGeometry.part X Y →
        K.toEffectiveGeometry.F (T h X) (T h Y) =
          K.toEffectiveGeometry.F X Y) := by
  classical
  -- A genuine H-action on the globally padded real-label carrier.
  let pi : H →* Equiv.Perm (Quotient D.part × V) := {
    toFun := fun h => Equiv.prodCongr (iota h) (tau h)
    map_one' := by
      apply Equiv.ext
      rintro ⟨i, x⟩
      change (iota (1 : H) i, tau (1 : H) x) = (i, x)
      simp
    map_mul' := by
      intro k h
      apply Equiv.ext
      rintro ⟨i, x⟩
      change (iota (k * h) i, tau (k * h) x) =
        (iota k (iota h i), tau k (tau h x))
      rw [map_mul, map_mul]
      rfl
  }
  have hpi (h : H) (z : Quotient D.part × V) :
      (pi h z).1 = iota h z.1 := rfl
  -- The padded imaginary sort is conjugate to the original quotient.
  let iotaP : H →* Equiv.Perm
      (Quotient D.uniformPaddedGeometry.part) := {
    toFun := fun h => D.paddedPartPermutation (iota h)
    map_one' := by
      apply Equiv.ext
      intro q
      change D.paddedClassEquiv.symm
        (iota (1 : H) (D.paddedClassEquiv q)) = q
      simp
    map_mul' := by
      intro k h
      apply Equiv.ext
      intro q
      change D.paddedClassEquiv.symm
        (iota (k * h) (D.paddedClassEquiv q)) =
          D.paddedClassEquiv.symm
            (iota k (iota h (D.paddedClassEquiv q)))
      rw [map_mul]
      rfl
  }
  have hcls (h : H) (z : Quotient D.part × V) :
      Quotient.mk D.uniformPaddedGeometry.part (pi h z) =
        iotaP h (Quotient.mk D.uniformPaddedGeometry.part z) :=
    (D.paddedPartPermutation_class (iota h) (pi h) (hpi h) z).symm
  -- Exact old-image compatibility only on the requested subgroup action.
  have hold (h : H) (x : S) :
      pi h (D.paddedOldMap x.val) =
        D.paddedOldMap (rho h x).val := by
    change (iota h (Quotient.mk D.part x.val), tau h x.val) =
      (Quotient.mk D.part (rho h x).val, (rho h x).val)
    exact Prod.ext (hIota h x) (hTau h x)
  obtain ⟨T, hTold, hTE, hTF⟩ :=
    exists_subsingletonEffectiveWitnessGroupLift
      D.uniformPaddedGeometry K pi iotaP hcls
  refine ⟨T, ?_, hTE, hTF⟩
  intro h x
  rw [hTold h (D.paddedOldMap x.val), hold h x]

end EffectiveGeometry

end SemigenericEPPA
