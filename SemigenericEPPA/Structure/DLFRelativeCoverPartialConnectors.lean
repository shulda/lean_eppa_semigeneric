import SemigenericEPPA.Algebra.DLFRelativeCoverSafeInvolutions
import SemigenericEPPA.Structure.ConstantNewPartRawGroupAction

/-!
# Every individual old connector survives the SAME split group cover

If a finite original raw witness has an action of an ambient group
Q containing individual automorphism extensions of some old partial
maps, replacing Q by its single fixed surjective relative cover
T → Q does not lose any extension. Any selected q in Q has a
preimage a in T, and the literal new-regular-E-class action of a
agrees with q on every old vertex. No coherent choice of connectors
is made or claimed.

This is the bridge between relative safe raw EPPA and the finite
involution-killing cover for the cofinal semi-coherent step.
-/

namespace SemigenericEPPA
namespace RelativeDLF

universe u v w
variable {Q : Type u} [Group Q]
variable {V : Type v} {A : Type w}

/-- A prescribed partial map whose vertices are extended by
some q ∈ Q is extended by an element of the SAME relative
finite cover, acting on the old summand of the actual new-class
permutation action. -/
theorem relativeCover_liftOldPartialConnector
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)]
    (rho : Q →* Equiv.Perm V)
    (e : A → V)
    (T : Set A) (p : T → A)
    (hQ : ∃ q : Q, ∀ x : T, rho q (e x.val) = e (p x)) :
    ∃ a : relativeBoundaryCover H,
      ∀ x : T,
        sumRawGroupAction
            (relativeCoverOldAction H rho)
            (rawLeftRegularAction (relativeBoundaryCover H))
            a (.inl (e x.val)) =
          (Sum.inl (e (p x)) : V ⊕ relativeBoundaryCover H) := by
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨a, ha⟩ := relativeCoverProjection_surjective H q
  refine ⟨a, ?_⟩
  intro x
  rw [sumRawGroupAction_inl]
  change (Sum.inl (rho (relativeCoverProjection H a) (e x.val)) :
    V ⊕ relativeBoundaryCover H) = .inl (e (p x))
  rw [ha, hq x]

/-- Surjectivity preserves not merely one but EVERY individual
old partial-map connector, on the same cover and the same embedding. -/
theorem relativeCover_liftAllOldPartialConnectors
    (H : Subgroup Q)
    [Fintype (CoverVertex H)] [Fintype (CoverEdge H)]
    (rho : Q →* Equiv.Perm V)
    (e : A → V)
    (hAll : ∀ (T : Set A) (p : T → A),
      Function.Injective p →
      ∃ q : Q, ∀ x : T, rho q (e x.val) = e (p x)) :
    ∀ (T : Set A) (p : T → A), Function.Injective p →
      ∃ a : relativeBoundaryCover H,
        ∀ x : T,
          sumRawGroupAction
              (relativeCoverOldAction H rho)
              (rawLeftRegularAction (relativeBoundaryCover H))
              a (.inl (e x.val)) =
            (Sum.inl (e (p x)) : V ⊕ relativeBoundaryCover H) := by
  intro T p hp
  exact relativeCover_liftOldPartialConnector H rho e T p (hAll T p hp)

end RelativeDLF
end SemigenericEPPA
