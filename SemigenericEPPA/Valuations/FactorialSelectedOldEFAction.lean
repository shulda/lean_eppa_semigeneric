import SemigenericEPPA.Valuations.NontrivialFactorialAuxiliaryAction
import SemigenericEPPA.Valuations.EmbeddedOldSubsetEquivariance

/-!
# One factorial auxiliary action is a genuine automorphism on old(S)

The bare factorial permutation of the fixed carrier was constructed
without imposing any effective F-invariance outside an induced
old subset S⊆A. The selected-image transfer theorem then shows
that exact agreement with H on the old copy suffices for E/F
invariance precisely on the image old(S).

We combine those two already independently certified constructions
for a SINGLE fixed original embedding
  old(x)=([x]_E,j(x)) : A→(A/E)×Fin(|A|!).

For each H acting by genuine E/F-automorphisms of S, construct one
strict group action tau on the SAME factorial old-label carrier,
together with an H-action on its old E-indices. We obtain:
* the correct index action on every padded label;
* exact pointwise extension of the original H-action on old(S);
* pointwise trivial action on unoccupied padded classes;
* H-invariance of the literal selected old image;
* preservation/reflection of E and preservation of ALL effective
  cross-E colours on that selected image.

No global F-invariance of tau is claimed. This is precisely the
correct input to the nontrivial-G occupied multiplier and reference
twist construction over the fixed auxiliary geometry.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {A : Type v} [Fintype A]
variable {H : Type w} [Group H]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- The old embedding into a prechosen factorial equal-fibre
carrier. It does not depend on a later S or H. -/
def factorialAuxiliaryOldMap
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (x : A) :
    Quotient D.part × Fin (coherentPaddingSize A) :=
  (Quotient.mk D.part x, j x)

/-- A group of genuine automorphisms of ANY selected induced old
S has a strictly compatible action on a prechosen factorial
auxiliary carrier. The resulting action preserves the original
effective E/F structure precisely on the selected old image.
No colour-preservation assumption is imposed on the complement.

Here B is a fixed effective E/F geometry independently constructed
over the factorial carrier. Its exact old E/F embedding is an
assumption; the explicit fixed constant-skeleton padding lemma
supplies B in the later main application. -/
theorem exists_factorialAuxiliaryAction_preservingSelectedEF
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (B : EffectiveGeometry s
      (Quotient D.part × Fin (coherentPaddingSize A)))
    (hBPart : ∀ z w : Quotient D.part × Fin (coherentPaddingSize A),
      B.part z w ↔ z.1 = w.1)
    (hBColour : ∀ x y : A, ¬D.part x y →
      B.F (D.factorialAuxiliaryOldMap j x)
        (D.factorialAuxiliaryOldMap j y) = D.F x y)
    (S : Set A)
    (rho : H →* Equiv.Perm S)
    (hE : ∀ (h : H) (x y : S),
      D.part (rho h x).val (rho h y).val ↔ D.part x.val y.val)
    (hF : ∀ (h : H) (x y : S), ¬D.part x.val y.val →
      D.F (rho h x).val (rho h y).val = D.F x.val y.val) :
    ∃ (iota : H →* Equiv.Perm (Quotient D.part))
      (tau : H →* Equiv.Perm
        (Quotient D.part × Fin (coherentPaddingSize A))),
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (tau h z).1 = iota h z.1) ∧
      (∀ (h : H) (x : S),
        tau h (D.factorialAuxiliaryOldMap j x.val) =
          D.factorialAuxiliaryOldMap j (rho h x).val) ∧
      (∀ (h : H) (i : Quotient D.part),
        (¬∃ x : S, Quotient.mk D.part x.val = i) →
          iota h i = i) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        (¬∃ x : S, Quotient.mk D.part x.val = z.1) →
          tau h z = z) ∧
      (∀ (h : H) (z : Quotient D.part × Fin (coherentPaddingSize A)),
        z ∈ embeddedOldSubset (D.factorialAuxiliaryOldMap j) S ↔
          tau h z ∈ embeddedOldSubset (D.factorialAuxiliaryOldMap j) S) ∧
      (∀ (h : H)
          (x y : {z : Quotient D.part × Fin (coherentPaddingSize A) //
            z ∈ embeddedOldSubset (D.factorialAuxiliaryOldMap j) S}),
        B.part (tau h x.val) (tau h y.val) ↔ B.part x.val y.val) ∧
      (∀ (h : H)
          (x y : {z : Quotient D.part × Fin (coherentPaddingSize A) //
            z ∈ embeddedOldSubset (D.factorialAuxiliaryOldMap j) S}),
        ¬B.part x.val y.val →
          B.F (tau h x.val) (tau h y.val) = B.F x.val y.val) := by
  obtain ⟨iota, tau, hIdx, hOld, hFixed, hUnused⟩ :=
    D.exists_factorialAuxiliaryGroupActions j hj S rho
      (by
        intro h x y
        exact (hE h x y).symm)
  let old : A → Quotient D.part × Fin (coherentPaddingSize A) :=
    D.factorialAuxiliaryOldMap j
  have hOld' : ∀ (h : H) (x : S),
      tau h (old x.val) = old (rho h x).val :=
    hOld
  have hPartOld : ∀ x y : A,
      B.part (old x) (old y) ↔ D.part x y := by
    intro x y
    change B.part (Quotient.mk D.part x, j x)
      (Quotient.mk D.part y, j y) ↔ D.part x y
    rw [hBPart]
    exact ⟨Quotient.exact, Quotient.sound⟩
  have hImage (h : H)
      (z : Quotient D.part × Fin (coherentPaddingSize A)) :
      z ∈ embeddedOldSubset old S ↔
        tau h z ∈ embeddedOldSubset old S :=
    embeddedOldSubset_invariant old S rho tau hOld' h z
  have hPartImage (h : H)
      (x y : {z : Quotient D.part × Fin (coherentPaddingSize A) //
          z ∈ embeddedOldSubset old S}) :
      B.part (tau h x.val) (tau h y.val) ↔
        B.part x.val y.val :=
    embeddedOldSubset_part_invariant
      D B old S hPartOld rho tau hOld' hE h x y
  have hColourImage (h : H)
      (x y : {z : Quotient D.part × Fin (coherentPaddingSize A) //
          z ∈ embeddedOldSubset old S})
      (hxy : ¬B.part x.val y.val) :
      B.F (tau h x.val) (tau h y.val) = B.F x.val y.val :=
    embeddedOldSubset_cross_invariant
      D B old S hPartOld hBColour rho tau hOld' hE hF
      h x y hxy
  exact ⟨iota, tau, hIdx, hOld, hFixed, hUnused,
    hImage, hPartImage, hColourImage⟩

end EffectiveGeometry

end SemigenericEPPA
