import SemigenericEPPA.Valuations.EffectiveAutomorphisms
import Mathlib.Tactic.Group

/-!
# The partial-map part-valuation permutation (3.17)--(3.18)

Given a permutation `ι` of the old imaginary parts, a permutation
`π` of the old real labels, and fixed twisting functions `L i : V → G`,
the formula

  σ (i,h) = (ι i, h'),    h' (π x) = L i x * h x

is an actual permutation of witness parts.  It fixes the neutral valuation
over every i for which L i is constantly 1.  If π respects ι on quotient
classes, it also gives bijections of the old-label fibres, hence an actual
automorphism of the effective valuation witness by the previous module.

This is the permutation/old-label component of manuscript (3.16)--(3.19).
Choosing the twists and skeleton multipliers to extend an arbitrary
given partial automorphism remains a separate EPPA obligation.
-/

namespace SemigenericEPPA

universe u v

variable {G : Type u} [Group G] {V : Type v}
variable {s : AffineAntiInvolution G}

/-- The affine permutation of the full function valuation sort:
h'(π x)=L(x)h(x). No commutativity of G is assumed. -/
def twistPartValuation
    (π : V ≃ V) (L : V → G) : (V → G) ≃ (V → G) where
  toFun := fun h y => L (π.symm y) * h (π.symm y)
  invFun := fun h x => (L x)⁻¹ * h (π x)
  left_inv := by
    intro h
    funext x
    change (L x)⁻¹ * (L (π.symm (π x)) * h (π.symm (π x))) = h x
    simp only [Equiv.symm_apply_apply]
    group
  right_inv := by
    intro h
    funext y
    change L (π.symm y) *
        ((L (π.symm y))⁻¹ * h (π (π.symm y))) = h y
    simp only [Equiv.apply_symm_apply]
    group

/-- Formula (3.17) at an arbitrary old vertex. -/
theorem twistPartValuation_apply_at
    (π : V ≃ V) (L : V → G) (h : V → G) (x : V) :
    twistPartValuation π L h (π x) = L x * h x := by
  change L (π.symm (π x)) * h (π.symm (π x)) = L x * h x
  rw [π.symm_apply_apply]

/-- Formula (3.18): permute old part indices and twist each valuation
independently by its own fixed function L i. -/
def twistedWitnessPartPerm
    (D : EffectiveGeometry s V)
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G) :
    EffectiveWitnessPart D ≃ EffectiveWitnessPart D where
  toFun := fun q => ⟨ι q.1, twistPartValuation π (L q.1) q.2⟩
  invFun := fun q =>
    ⟨ι.symm q.1,
      (twistPartValuation π (L (ι.symm q.1))).symm q.2⟩
  left_inv := by
    rintro ⟨i, h⟩
    apply Prod.ext
    · exact ι.symm_apply_apply i
    · change (twistPartValuation π (L (ι.symm (ι i)))).symm
        (twistPartValuation π (L i) h) = h
      rw [ι.symm_apply_apply]
      exact (twistPartValuation π (L i)).symm_apply_apply h
  right_inv := by
    rintro ⟨i, h⟩
    apply Prod.ext
    · exact ι.apply_symm_apply i
    · change twistPartValuation π (L (ι.symm i))
        ((twistPartValuation π (L (ι.symm i))).symm h) = h
      exact (twistPartValuation π (L (ι.symm i))).apply_symm_apply h

@[simp] theorem twistedWitnessPartPerm_fst
    (D : EffectiveGeometry s V)
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G)
    (q : EffectiveWitnessPart D) :
    (twistedWitnessPartPerm D ι π L q).1 = ι q.1 := rfl

/-- The TARGET-part group function transforms exactly as (3.17),
with order L(x)*h(x), never the reverse order. -/
theorem twistedWitnessPartPerm_valuation
    (D : EffectiveGeometry s V)
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G)
    (q : EffectiveWitnessPart D) (x : V) :
    (twistedWitnessPartPerm D ι π L q).2 (π x) =
      L q.1 x * q.2 x := by
  exact twistPartValuation_apply_at π (L q.1) q.2 x

/-- If L is trivial on part i, its distinguished neutral witness
part goes to the distinguished neutral witness part over ι(i). -/
theorem twistedWitnessPartPerm_distinguished
    (D : EffectiveGeometry s V)
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G)
    (i : Quotient D.part)
    (hL : ∀ x : V, L i x = 1) :
    twistedWitnessPartPerm D ι π L (distinguishedWitnessPart D i) =
      distinguishedWitnessPart D (ι i) := by
  apply Prod.ext
  · rfl
  · funext y
    change L i (π.symm y) * neutralPartValuation (π.symm y) =
      neutralPartValuation y
    simp [neutralPartValuation, hL]

/-- When the old real-label permutation π induces ι on the E-quotient,
it restricts to an actual equivalence of each old-label fibre over q
with the fibre over σ(q). Part valuations do not alter fibre size. -/
def twistedWitnessFibreEquiv
    (D : EffectiveGeometry s V)
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G)
    (hπ : ∀ x : V,
      Quotient.mk D.part (π x) = ι (Quotient.mk D.part x))
    (q : EffectiveWitnessPart D) :
    EffectiveWitnessFibre D q ≃
      EffectiveWitnessFibre D (twistedWitnessPartPerm D ι π L q) where
  toFun := fun x =>
    ⟨π x.1, by
      change Quotient.mk D.part (π x.1) = ι q.1
      rw [hπ, x.2]⟩
  invFun := fun y =>
    ⟨π.symm y.1, by
      have hx := hπ (π.symm y.1)
      rw [π.apply_symm_apply] at hx
      have hy : Quotient.mk D.part y.1 = ι q.1 := y.2
      change Quotient.mk D.part (π.symm y.1) = q.1
      apply ι.injective
      exact hx.symm.trans hy⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact π.symm_apply_apply x.1
  right_inv := by
    intro y
    apply Subtype.ext
    exact π.apply_symm_apply y.1

/-- The selected σ and fibre bijections instantiate the checked
two-layer effective-witness automorphism theorem. -/
noncomputable def twistedWitnessAutomorphism
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G)
    (hπ : ∀ x : V,
      Quotient.mk D.part (π x) = ι (Quotient.mk D.part x)) :
    EffectiveWitnessVertex D ≃ EffectiveWitnessVertex D :=
  effectiveWitnessAutomorphism D K (twistedWitnessPartPerm D ι π L)
    (twistedWitnessFibreEquiv D ι π L hπ)

/-- The true old-label coordinate of any witness vertex is sent
to π(x). This is the real-coordinate part of the extension equation. -/
theorem twistedWitnessAutomorphism_old
    (D : EffectiveGeometry s V)
    (K : EffectiveWitnessSkeleton D)
    [LinearOrder (EffectiveWitnessPart D)]
    (ι : Quotient D.part ≃ Quotient D.part)
    (π : V ≃ V)
    (L : Quotient D.part → V → G)
    (hπ : ∀ x : V,
      Quotient.mk D.part (π x) = ι (Quotient.mk D.part x))
    (X : EffectiveWitnessVertex D) :
    (twistedWitnessAutomorphism D K ι π L hπ X).old = π X.old := by
  change (witnessVertexTransportEquiv D
      (twistedWitnessPartPerm D ι π L)
      (twistedWitnessFibreEquiv D ι π L hπ)
      (globallyForcedWitnessMultiplier s K.colour
        (twistedWitnessPartPerm D ι π L)) X).old = π X.old
  rw [witnessVertexTransportEquiv_apply, transportWitnessVertex_old]
  rfl

end SemigenericEPPA
