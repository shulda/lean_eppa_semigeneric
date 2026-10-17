import SemigenericEPPA.Valuations.PrescribedAutomorphism

/-!
# Exact extension criterion for individual old vertices

The final E0 extension proof must show that the constructed automorphism
takes the literal old witness vertex of x to that of p(x). The source
and target parts, old real labels, and all cross-part effective incidence
coordinates jointly determine a witness vertex.

We first prove the associated exact extensionality theorem. We then
apply the prescribed multiplier automorphism: to prove it extends x↦y,
it suffices to show (1) σ sends x's neutral part to y's, (2) the
fibre map sends the old label x to y, (3) for each other witness part r,
the prescribed multiplier a converts λ_old(x)(r) to
λ_old(y)(σ r). No global EPPA theorem is assumed.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

namespace EffectiveWitnessVertex

/-- The full set of target-part incidence coordinates, together
with the actual source part and old label, determines the complete
two-layer valuation witness vertex. -/
theorem eq_of_crossIncidence
    {D : EffectiveGeometry s V}
    (X Y : EffectiveWitnessVertex D)
    (hpart : X.part = Y.part)
    (hold : X.old = Y.old)
    (hinc : ∀ (r : EffectiveWitnessPart D)
      (hrX : r ≠ X.part) (hrY : r ≠ Y.part),
      X.crossIncidence r hrX = Y.crossIncidence r hrY) :
    X = Y := by
  cases X with
  | mk q x hx χ =>
    cases Y with
    | mk q' y hy ψ =>
      dsimp at hpart hold
      cases hpart
      cases hold
      have hv : χ = ψ := by
        funext r
        have heq := hinc r.1 r.2 r.2
        change χ r * r.1.2 x = ψ r * r.1.2 x at heq
        exact mul_right_cancel heq
      cases hv
      rfl

end EffectiveWitnessVertex

/-- Concrete old-vertex extension criterion for prescribed compatible
multipliers. Hypotheses are precisely the conditions supplied by
(3.14), (3.16)--(3.19), once the old partial isomorphism has provided
the permutation of old part indices and a global real-label bijection.

The compatibility between prescribed multipliers is needed only to
make the resulting total automorphism preserve every effective colour;
the literal pointwise extension calculation itself uses incidence
and old-label transport. -/
theorem prescribedEffectiveWitnessAutomorphism_maps_old
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (σ : EffectiveWitnessPart D ≃ EffectiveWitnessPart D)
    (ρ : ∀ q : EffectiveWitnessPart D,
      EffectiveWitnessFibre D q ≃ EffectiveWitnessFibre D (σ q))
    (P : EffectiveWitnessPart D → Prop)
    (a : EffectiveWitnessPart D → EffectiveWitnessPart D → G)
    (x y : V)
    (hP : P (oldWitnessPart D x))
    (hpart : σ (oldWitnessPart D x) = oldWitnessPart D y)
    (hold : (ρ (oldWitnessPart D x) ⟨x, rfl⟩).val = y)
    (hinc : ∀ (r : EffectiveWitnessPart D)
        (hr : r ≠ oldWitnessPart D x),
      a (oldWitnessPart D x) r *
          (D.oldWitnessVertex x).crossIncidence r hr =
        (D.oldWitnessVertex y).crossIncidence (σ r) (by
          intro heq
          apply hr
          apply σ.injective
          exact heq.trans hpart.symm)) :
    prescribedEffectiveWitnessAutomorphism D K σ ρ P a
      (D.oldWitnessVertex x) = D.oldWitnessVertex y := by
  let X := D.oldWitnessVertex x
  let Y := D.oldWitnessVertex y
  let T := prescribedEffectiveWitnessAutomorphism D K σ ρ P a
  apply EffectiveWitnessVertex.eq_of_crossIncidence (T X) Y
  · exact (prescribedEffectiveWitnessAutomorphism_part
      D K σ ρ P a X).trans hpart
  · exact (prescribedEffectiveWitnessAutomorphism_old
      D K σ ρ P a X).trans hold
  · intro r hrT hrY
    let u : EffectiveWitnessPart D := σ.symm r
    have hu : u ≠ X.part := by
      intro heq
      apply hrT
      calc
        r = σ u := (σ.apply_symm_apply r).symm
        _ = σ X.part := congrArg σ heq
        _ = (T X).part :=
          (prescribedEffectiveWitnessAutomorphism_part
            D K σ ρ P a X).symm
    have htransport :=
      prescribedEffectiveWitnessAutomorphism_incidence
        D K σ ρ P a X u hu hP
    have htarget := hinc u hu
    have hresult := htransport.trans htarget
    simpa only [Equiv.apply_symm_apply] using hresult

end SemigenericEPPA
