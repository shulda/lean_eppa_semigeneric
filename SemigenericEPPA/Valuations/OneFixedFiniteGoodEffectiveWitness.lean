import SemigenericEPPA.Structure.FixedGoodFactorialEffectiveBase
import SemigenericEPPA.Structure.IndexedGaugeReindexing
import SemigenericEPPA.Valuations.FixedGaugeFactorialRelativeHAction
import SemigenericEPPA.Valuations.GaugeOldEffectiveEmbedding
import SemigenericEPPA.Valuations.FixedSkeletonExtensionality
import SemigenericEPPA.Valuations.WitnessFiniteness

/-!
# ONE finite effective witness and every selected-substructure H-action

This theorem fixes a single finite two-layer valuation geometry,
a constant genuinely good skeleton, and a LITERAL old vertex
embedding before selecting ANY induced substructure S or group H.
In particular, neither the old zero-section nor any witness
valuation part, raw effective colour or gauge representation is
rechosen as S or H varies.

The construction starts with one normalized finite old effective
geometry D. The fixed factorial indexed gauge Q over
(A/E)×Fin(|A|!) is built before all S/H. A single fixed
quotient-indexed gauge R is chosen via the canonical equivalence
Quotient(Q.part)≃A/E; its old incidence rows are also fixed.
The full two-layer witness B is the one associated to Q and
its genuinely fixed good skeleton K0.

For ANY subsequently chosen group H acting by genuine E/F
automorphisms of an induced S⊆A, the certified relative theorem
supplies the auxiliary factorial H-action, quotient H-action,
strict old-index multipliers and reference twists. The resulting
strict Theta:H→Perm(EffectiveWitnessVertex B) preserves ALL
effective witness E/F and extends the SAME old zero-section.

Skeleton extensionality makes the group-dependent existential
constant-g0 skeleton from the relative theorem literally equal
to K0; no H-dependent witness is substituted.

This completes the fixed-quantifier-order positive EFFECTIVE
finite-group action statement for arbitrary nonabelian G. It
does NOT yet include the raw flip-safe cover, ordinary raw-colour
extension, or final coherent EPPA groupoid theorem.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- One common FINITE two-layer effective witness and literal
E/F-induced old embedding supporting homomorphic extensions of
every selected old E/F automorphism group, with quantifiers
`∃ B, K, ψ, ∀ S,H,ρ, ∃ Θ`.

The fixed witness carrier is the complete two-layer valuation
sort of a factorial-padded auxiliary old-label geometry. Its
original skeleton is prechosen as the genuine good fixed colour.
All later actions preserve that very witness geometry strictly. -/
theorem exists_oneFiniteGoodEffectiveWitness_allRelativeGroupActions
    (D : EffectiveGeometry d.s A)
    (hSame : ∀ x y : A, D.part x y → D.F x y = 1)
    (hGood : d.selfReverseEffective.Nonempty) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (Q : IndexedGauge d.s
        (Quotient D.part × Fin (coherentPaddingSize A))
        (Quotient D.part))
      (R : IndexedGauge d.s
        (Quotient D.part × Fin (coherentPaddingSize A))
        (Quotient Q.toEffectiveGeometry.part))
      (K : EffectiveWitnessSkeleton Q.toEffectiveGeometry),
      let B := Q.toEffectiveGeometry
      let ψ : A → EffectiveWitnessVertex B :=
        fun x => B.gaugeOldWitnessVertex R.vertexGauge
          (D.factorialAuxiliaryOldMap j x)
      Function.Injective ψ ∧
      (∀ x y : A,
        K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ D.part x y) ∧
      (∀ x y : A, ¬D.part x y →
        K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y) ∧
      Finite (EffectiveWitnessVertex B) ∧
      (∀ (H : Type t) [Group H]
        (S : Set A) (ρ : H →* Equiv.Perm S),
        (∀ (h : H) (x y : S),
          D.part (ρ h x).val (ρ h y).val ↔
            D.part x.val y.val) →
        (∀ (h : H) (x y : S), ¬D.part x.val y.val →
          D.F (ρ h x).val (ρ h y).val = D.F x.val y.val) →
        ∃ Θ : H →* Equiv.Perm (EffectiveWitnessVertex B),
          (∀ (h : H) (x : S),
            Θ h (ψ x.val) = ψ (ρ h x).val) ∧
          (∀ (h : H) (X Y : EffectiveWitnessVertex B),
            K.toEffectiveGeometry.part (Θ h X) (Θ h Y) ↔
              K.toEffectiveGeometry.part X Y) ∧
          (∀ (h : H) (X Y : EffectiveWitnessVertex B),
            ¬K.toEffectiveGeometry.part X Y →
              K.toEffectiveGeometry.F (Θ h X) (Θ h Y) =
                K.toEffectiveGeometry.F X Y)) := by
  classical
  let W := Quotient D.part × Fin (coherentPaddingSize A)
  obtain ⟨j, P, Q, hj, hPLabel, _hPConstant, _hPDiag,
      hQData, _hPOldE, hPOldF, hFiniteW⟩ :=
    D.exists_fixedGoodFactorialEffectiveBase hSame hGood
  let B : EffectiveGeometry d.s W := Q.toEffectiveGeometry
  have hQLabel (z : W) : Q.label z = z.1 :=
    (hQData z).1
  have hQDiag (z : W) : Q.vertexGauge z z.1 = 1 :=
    (hQData z).2
  let g0 : G := Classical.choose hGood
  have hGoodFixed : d.s g0 = g0 :=
    d.selfReverseEffective_subset_fixed (Classical.choose_spec hGood)
  have hQConst (i k : Quotient D.part) :
      Q.skeleton i k = g0 := by
    -- The globally fixed padded skeleton is definitionally constant.
    rfl
  have hPositive : 0 < coherentPaddingSize A :=
    coherentPaddingSize_pos A
  obtain ⟨R, hRLabel, hRConst, hRDiag, _hRPart, hRF⟩ :=
    exists_fixedFibreGauge_onActualQuotient
      (s := d.s) (coherentPaddingSize A) hPositive Q
      hQLabel g0 hQConst
  have hRDiagOne (z : W) :
      R.vertexGauge z (R.label z) = 1 := by
    rw [hRDiag z, hQLabel z]
    exact hQDiag z
  let old : A → W := D.factorialAuxiliaryOldMap j
  have hOldMap (x : A) :
      P.fixedUniformPaddingOldMap j x = old x := by
    change (P.label x, j x) = (Quotient.mk D.part x, j x)
    rw [hPLabel x]
  have hBaseE (x y : A) :
      B.part (old x) (old y) ↔ D.part x y := by
    change Q.label (old x) = Q.label (old y) ↔ D.part x y
    rw [hQLabel (old x), hQLabel (old y)]
    change (Quotient.mk D.part x = Quotient.mk D.part y) ↔ D.part x y
    exact ⟨Quotient.exact, Quotient.sound⟩
  have hBaseF (x y : A) (hxy : ¬D.part x y) :
      B.F (old x) (old y) = D.F x y := by
    rw [← hOldMap x, ← hOldMap y]
    exact hPOldF x y hxy
  have hROldF (x y : W) (_hxy : ¬B.part x y) :
      R.effective x y = B.F x y :=
    hRF x y
  let skeleton : Quotient B.part → Quotient B.part → G :=
    fun _ _ => g0
  have hReverse : ∀ i k : Quotient B.part,
      skeleton k i = d.s (skeleton i k) := by
    intro i k
    exact hGoodFixed.symm
  let K : EffectiveWitnessSkeleton B :=
    B.indexedWitnessSkeleton skeleton hReverse
  have hKConst (q r : EffectiveWitnessPart B) :
      K.colour q r = g0 := rfl
  have hKOld (i k : Quotient B.part) (_ : i ≠ k) :
      K.colour (distinguishedWitnessPart B i)
        (distinguishedWitnessPart B k) = R.skeleton i k :=
    (hKConst _ _).trans (hRConst i k).symm
  let ψ : A → EffectiveWitnessVertex B :=
    fun x => B.gaugeOldWitnessVertex R.vertexGauge (old x)
  have hInjective : Function.Injective ψ := by
    intro x y hxy
    have hold : old x = old y :=
      B.gaugeOldWitnessVertex_injective R.vertexGauge hxy
    exact hj (congrArg Prod.snd hold)
  have hψE (x y : A) :
      K.toEffectiveGeometry.part (ψ x) (ψ y) ↔ D.part x y :=
    (B.gaugeOldWitnessVertex_part_iff
      R.vertexGauge K (old x) (old y)).trans (hBaseE x y)
  have hψF (x y : A) (hxy : ¬D.part x y) :
      K.toEffectiveGeometry.F (ψ x) (ψ y) = D.F x y := by
    have hcross : ¬B.part (old x) (old y) := by
      intro hb
      exact hxy ((hBaseE x y).mp hb)
    calc
      K.toEffectiveGeometry.F (ψ x) (ψ y) =
        B.F (old x) (old y) :=
          B.gaugeOldWitnessVertex_colour
            R hRLabel hROldF K hKOld (old x) (old y) hcross
      _ = D.F x y := hBaseF x y hxy
  have hFiniteWitness : Finite (EffectiveWitnessVertex B) := by
    letI : Finite W := hFiniteW
    exact B.finite_effectiveWitnessVertices
  have hAll : ∀ (H : Type t) [Group H]
      (S : Set A) (ρ : H →* Equiv.Perm S),
      (∀ (h : H) (x y : S),
        D.part (ρ h x).val (ρ h y).val ↔ D.part x.val y.val) →
      (∀ (h : H) (x y : S), ¬D.part x.val y.val →
        D.F (ρ h x).val (ρ h y).val = D.F x.val y.val) →
      ∃ Θ : H →* Equiv.Perm (EffectiveWitnessVertex B),
        (∀ (h : H) (x : S),
          Θ h (ψ x.val) = ψ (ρ h x).val) ∧
        (∀ (h : H) (X Y : EffectiveWitnessVertex B),
          K.toEffectiveGeometry.part (Θ h X) (Θ h Y) ↔
            K.toEffectiveGeometry.part X Y) ∧
        (∀ (h : H) (X Y : EffectiveWitnessVertex B),
          ¬K.toEffectiveGeometry.part X Y →
            K.toEffectiveGeometry.F (Θ h X) (Θ h Y) =
              K.toEffectiveGeometry.F X Y) := by
    intro H _ S ρ hE hF
    obtain ⟨K', Θ, hK', hOld, hETheta, hFTheta⟩ :=
      D.exists_factorialRelativeHAction_onFixedGauge
        hGood j hj Q hQLabel hBaseF
        R hRLabel hRConst hRDiagOne hRF S ρ hE hF
    have hEq : K' = K :=
      K'.eq_of_sameConstant K g0 hK' hKConst
    refine ⟨Θ, ?_, ?_, ?_⟩
    · intro h x
      exact hOld h x
    · simpa only [hEq] using hETheta
    · simpa only [hEq] using hFTheta
  exact ⟨j, Q, R, K, hInjective, hψE, hψF, hFiniteWitness, hAll⟩

end EffectiveGeometry

end SemigenericEPPA
