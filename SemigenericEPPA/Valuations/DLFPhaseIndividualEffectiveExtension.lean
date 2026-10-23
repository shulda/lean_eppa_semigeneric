import SemigenericEPPA.Valuations.RelativePhaseEffectiveSafety

/-!
# Individual effective partial extensions survive regular phase expansion

The relative safe-group EPPA proof starts with A⊆B and a finite
effective witness W for B supporting:
* one strict H-action extending the prescribed action on A;
* INDIVIDUAL (not coherent) automorphism extensions of all old
  partial maps of B.

Adding regular H phases over W is essential to force any H-element
that swaps vertices outside the old A sector to have square one.
The phase action, however, must not lose individual B extensions.

For any effective automorphism θ∈Aut_E/F(W), simply act as
(θ(x),r) on phase-expanded vertices (x,r). This is a genuine
E/F automorphism of the SAME phase-pulled-back geometry and
extends the old phase-one embedding exactly. It is independent
of the prescribed H group action; there is no request for its
extension to commute with H.

This is the individual effective connector half of relative
safe EPPA, separate from the raw cover lift and old raw return
consistency.
-/

namespace SemigenericEPPA

universe u v w z
variable {G : Type u} [Group G]
variable {V : Type v} {U : Type w}
variable {H : Type z} [Group H]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Every individual E/F automorphism of a finite base extends
to the phase pullback by acting on first coordinates only. -/
theorem phasePullback_liftIndividualEffectiveAut
    (D : EffectiveGeometry s V)
    (theta : Equiv.Perm V)
    (hE : ∀ x y : V,
      D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y : V, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y) :
    ∃ Theta : Equiv.Perm (V × H),
      (∀ (x : V) (r : H),
        Theta (x,r) = (theta x,r)) ∧
      (∀ X Y : V × H,
        (D.phasePullback H).part (Theta X) (Theta Y) ↔
          (D.phasePullback H).part X Y) ∧
      (∀ X Y : V × H,
        ¬(D.phasePullback H).part X Y →
        (D.phasePullback H).F (Theta X) (Theta Y) =
          (D.phasePullback H).F X Y) := by
  let Theta : Equiv.Perm (V × H) :=
    Equiv.prodCongr theta (Equiv.refl H)
  refine ⟨Theta, ?_, ?_, ?_⟩
  · intro x r
    rfl
  · intro X Y
    exact hE X.1 Y.1
  · intro X Y hcross
    exact hF X.1 Y.1 hcross

/-- In particular, every partial old map already lifted by
theta on one fixed base embedding e is also lifted on the SAME
phase-one old embedding. No extra hypotheses on H or the subset
of vertices carrying the group action. -/
theorem phasePullback_liftIndividualOldPartial
    (D : EffectiveGeometry s V)
    (e : U → V)
    (S : Set U) (p : S → U)
    (theta : Equiv.Perm V)
    (hext : ∀ x : S, theta (e x.val) = e (p x))
    (hE : ∀ x y : V,
      D.part (theta x) (theta y) ↔ D.part x y)
    (hF : ∀ x y : V, ¬D.part x y →
      D.F (theta x) (theta y) = D.F x y) :
    ∃ Theta : Equiv.Perm (V × H),
      (∀ x : S, Theta (e x.val,(1 : H)) = (e (p x),(1 : H))) ∧
      (∀ X Y : V × H,
        (D.phasePullback H).part (Theta X) (Theta Y) ↔
          (D.phasePullback H).part X Y) ∧
      (∀ X Y : V × H,
        ¬(D.phasePullback H).part X Y →
        (D.phasePullback H).F (Theta X) (Theta Y) =
          (D.phasePullback H).F X Y) := by
  obtain ⟨Theta, hTheta, hPart, hColour⟩ :=
    D.phasePullback_liftIndividualEffectiveAut (H := H) theta hE hF
  refine ⟨Theta, ?_, hPart, hColour⟩
  intro x
  rw [hTheta (e x.val) 1, hext x]

end EffectiveGeometry

end SemigenericEPPA
