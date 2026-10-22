import SemigenericEPPA.Valuations.FactorialSelectedOccupiedEFPackage
import SemigenericEPPA.Structure.IndexedGaugeReindexing

/-!
# The same occupied factorial H-action preserves selected INDEXED gauge F

The fixed factorial replica theorem returns a strict old-label
action tau, an actual-quotient index action iotaQ, and one
equivariant occupied Option-projection. The selected old zero-copy
labels are tau-invariant, and their B-effective F is preserved.

The selected multipliers used by the full two-layer valuation
construction are defined for a separately fixed quotient-indexed
gauge P which presents exactly B. Therefore we must show that
the VERY SAME tau preserves P.toEffectiveGeometry.F on the
literal selected old image, not introduce an unrelated action.

This is an exact noncommutative, no-global-F bridge: P and B
need only agree on all genuine cross-class pairs. Unoccupied
padded labels are free to have non-invariant F.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {A : Type v} [Fintype A]
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

/-- One actual factorial indexed-gauge selected H-action, complete
with its true-quotient occupied projection. Every selected cross
pair is F-invariant in the chosen gauge presentation itself. -/
theorem IndexedGauge.exists_factorialSelectedGaugeAction_withProjection
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (B : EffectiveGeometry s
      (Quotient D.part × Fin (coherentPaddingSize A)))
    (hBPart : ∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
      B.part z w ↔ z.1 = w.1)
    (hBOldF : ∀ x y : A, ¬D.part x y →
      B.F (Quotient.mk D.part x, j x)
        (Quotient.mk D.part y, j y) = D.F x y)
    (P : IndexedGauge s
      (Quotient D.part × Fin (coherentPaddingSize A))
      (Quotient B.part))
    (hPLabel : ∀ z : Quotient D.part × Fin (coherentPaddingSize A),
      P.label z = Quotient.mk B.part z)
    (hPF : ∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
      ¬B.part z w → P.effective z w = B.F z w)
    (S : Set A)
    (rhoS : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part x.val y.val ↔
        D.part (rhoS h x).val (rhoS h y).val)
    (hF : ∀ (h : H) (x y : S),
      ¬D.part x.val y.val →
        D.F (rhoS h x).val (rhoS h y).val = D.F x.val y.val) :
    ∃ (iotaQ : H →* Equiv.Perm (Quotient B.part))
      (tau : H →* Equiv.Perm
        (Quotient D.part × Fin (coherentPaddingSize A)))
      (proj : (Quotient D.part × Fin (coherentPaddingSize A)) →
        Option S),
      let old : S → Quotient D.part × Fin (coherentPaddingSize A) :=
        fun x => (Quotient.mk D.part x.val, j x.val)
      let cls : S → Quotient B.part :=
        fun x => Quotient.mk B.part (old x)
      let selected : Set
        (Quotient D.part × Fin (coherentPaddingSize A)) :=
          Set.range old
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        Quotient.mk B.part (tau h z) =
          iotaQ h (Quotient.mk B.part z)) ∧
      (∀ (h : H) (x : S),
        tau h (old x) = old (rhoS h x)) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        z ∈ selected ↔ tau h z ∈ selected) ∧
      (∀ (h : H) (q : Quotient B.part),
        (¬∃ x : S, cls x = q) → iotaQ h q = q) ∧
      (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
        (∃ x : S, cls x = Quotient.mk B.part z) →
          ∃ x : S, proj z = some x) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        proj (tau h z) = Option.map (rhoS h) (proj z)) ∧
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A)) (x : S),
        proj z = some x → Quotient.mk B.part z = cls x) ∧
      (∀ x : S, proj (old x) = some x) ∧
      (∀ x y : S, D.part x.val y.val ↔ cls x = cls y) ∧
      (∀ (h : H) (x y : selected),
        P.label x.val ≠ P.label y.val →
          P.toEffectiveGeometry.F (tau h x.val) (tau h y.val) =
            P.toEffectiveGeometry.F x.val y.val) := by
  obtain ⟨iotaQ, tau, proj, hIndex, hOld, hStable,
      hFixed, hSome, hProj, hProjClass, hOldProj, hClass, hSelectedF⟩ :=
    D.exists_factorialProjection_withSelectedEF
      j hj B hBPart hBOldF S rhoS hE hF
  let W : Type _ := Quotient D.part × Fin (coherentPaddingSize A)
  let old : S → W :=
    fun x => (Quotient.mk D.part x.val, j x.val)
  let cls : S → Quotient B.part :=
    fun x => Quotient.mk B.part (old x)
  let selected : Set W := Set.range old
  have hTauPart (h : H) (x y : W)
      (hxy : ¬B.part x y) :
      ¬B.part (tau h x) (tau h y) := by
    intro hn
    have heq : Quotient.mk B.part (tau h x) =
        Quotient.mk B.part (tau h y) := Quotient.sound hn
    rw [hIndex h x, hIndex h y] at heq
    exact hxy (Quotient.exact ((iotaQ h).injective heq))
  have hSelectedPF (h : H) (x y : selected)
      (hxy : P.label x.val ≠ P.label y.val) :
      P.toEffectiveGeometry.F (tau h x.val) (tau h y.val) =
        P.toEffectiveGeometry.F x.val y.val := by
    have hCross : ¬B.part x.val y.val := by
      intro heq
      apply hxy
      rw [hPLabel x.val, hPLabel y.val]
      exact Quotient.sound heq
    have hFSelected : B.F (tau h x.val) (tau h y.val) =
        B.F x.val y.val := by
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      have hab : ¬B.part (old a) (old b) := by
        rw [ha, hb]
        exact hCross
      rw [← ha, ← hb]
      exact hSelectedF h a b hab
    calc
      P.toEffectiveGeometry.F (tau h x.val) (tau h y.val) =
          B.F (tau h x.val) (tau h y.val) :=
        hPF (tau h x.val) (tau h y.val) (hTauPart h x.val y.val hCross)
      _ = B.F x.val y.val := hFSelected
      _ = P.toEffectiveGeometry.F x.val y.val :=
        (hPF x.val y.val hCross).symm
  exact ⟨iotaQ, tau, proj, hIndex, hOld, hStable,
    hFixed, hSome, hProj, hProjClass, hOldProj, hClass, hSelectedPF⟩

end SemigenericEPPA
