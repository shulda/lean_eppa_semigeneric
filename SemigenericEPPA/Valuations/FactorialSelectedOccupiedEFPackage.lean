import SemigenericEPPA.Valuations.FactorialOccupiedActualQuotientProjection

/-!
# One factorial replica action preserves selected effective colours

The occupied projection and the auxiliary old-label permutation MUST
come from the same factorial replica coding. The already certified
actual-quotient projection API constructs both, and returns the
unoccupied-class fixed-point and exact projection laws.

Here we prove a further property of that VERY permutation tau:
on the embedded genuinely selected old points it preserves E/F,
as soon as the fixed padded base has the known literal old E/F
embedding and the original selected H-action preserves E/F.

We do NOT claim that tau preserves F on unselected padded pairs.
The output also gives the selected-image stability, exact
old class/quotient identification, and all projection data needed
for the selected indexed-gauge raw flip-safety interface.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {A : Type v} [Fintype A]
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

/-- The SAME factorial auxiliary action is E/F-preserving on
the actual selected old zero-copy image, with occupied projection
on the true E-quotient of the fixed padded base. -/
theorem EffectiveGeometry.exists_factorialProjection_withSelectedEF
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
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (∃ x : S, cls x = Quotient.mk B.part z) →
          ∃ x : S, proj z = some x) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        proj (tau h z) = Option.map (rhoS h) (proj z)) ∧
      (∀ (z : Quotient D.part × Fin (coherentPaddingSize A)) (x : S),
        proj z = some x → Quotient.mk B.part z = cls x) ∧
      (∀ x : S, proj (old x) = some x) ∧
      (∀ x y : S, D.part x.val y.val ↔ cls x = cls y) ∧
      (∀ (h : H) (x y : S),
        ¬B.part (old x) (old y) →
          B.F (tau h (old x)) (tau h (old y)) =
            B.F (old x) (old y)) := by
  obtain ⟨iotaQ, tau, proj, hIndex, hOld, hFixed,
      hSome, hProj, hProjClass, hOldProj⟩ :=
    D.exists_factorialProjection_onActualQuotient
      j hj B hBPart S rhoS hE
  let W : Type _ := Quotient D.part × Fin (coherentPaddingSize A)
  let old : S → W :=
    fun x => (Quotient.mk D.part x.val, j x.val)
  let cls : S → Quotient B.part :=
    fun x => Quotient.mk B.part (old x)
  let selected : Set W := Set.range old
  have hStable : ∀ (h : H) (z : W),
      z ∈ selected ↔ tau h z ∈ selected := by
    intro h z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨rhoS h x, (hOld h x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨rhoS h⁻¹ x, ?_⟩
      apply (tau h).injective
      calc
        tau h (old (rhoS h⁻¹ x)) = old x := by
          rw [hOld h]
          simp [old]
        _ = tau h z := hx
  have hOldPart (x y : S) :
      B.part (old x) (old y) ↔ D.part x.val y.val := by
    apply (hBPart (old x) (old y)).trans
    exact ⟨Quotient.exact, Quotient.sound⟩
  have hClass (x y : S) :
      D.part x.val y.val ↔ cls x = cls y := by
    exact (hOldPart x y).symm.trans
      (show B.part (old x) (old y) ↔ cls x = cls y
        from ⟨Quotient.sound, Quotient.exact⟩)
  have hSelectedF (h : H) (x y : S)
      (hxyB : ¬B.part (old x) (old y)) :
      B.F (tau h (old x)) (tau h (old y)) =
        B.F (old x) (old y) := by
    have hxy : ¬D.part x.val y.val := by
      intro hab
      exact hxyB ((hOldPart x y).mpr hab)
    have hnew : ¬D.part (rhoS h x).val (rhoS h y).val := by
      intro hab
      exact hxy ((hE h x y).mpr hab)
    calc
      B.F (tau h (old x)) (tau h (old y)) =
          B.F (old (rhoS h x)) (old (rhoS h y)) := by
            rw [hOld h x, hOld h y]
      _ = D.F (rhoS h x).val (rhoS h y).val :=
        hBOldF (rhoS h x).val (rhoS h y).val hnew
      _ = D.F x.val y.val := hF h x y hxy
      _ = B.F (old x) (old y) :=
        (hBOldF x.val y.val hxy).symm
  exact ⟨iotaQ, tau, proj, hIndex, hOld, hStable,
    hFixed, hSome, hProj, hProjClass, hOldProj, hClass, hSelectedF⟩

end SemigenericEPPA
