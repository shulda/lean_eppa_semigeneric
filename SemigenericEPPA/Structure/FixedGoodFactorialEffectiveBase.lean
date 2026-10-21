import SemigenericEPPA.Structure.FixedConstantGaugePadding
import SemigenericEPPA.Structure.ConstantGaugeDiagonal
import SemigenericEPPA.Algebra.FixedFactorialOldInjection

/-!
# A single fixed factorial effective E/F base for all later old groups

Let A be any finite old affine E-rectangle geometry, normalized by
F(x,y)=1 when x E y, and suppose the raw datum has one genuine
self-reversing effective colour g0.

This theorem chooses all finite geometric data BEFORE any later
induced substructure S⊆A, group H, or partial isomorphism:

* one ordering of the old quotient E-class imaginary sort I=A/E;
* one universal fixed injection j:A→Fin(|A|!);
* one constant-skeleton indexed gauge P on A with skeleton g0,
  exactly reconstructing the original effective cross-E colours;
* one indexed gauge Q on the fixed padded carrier
    W=(A/E)×Fin(|A|!)
  with the same constant skeleton g0 and normalized diagonal 1;
* the fixed old embedding x↦([x],j(x)), which is injective,
  E-induced and preserves literally EVERY cross-E group colour.

No group action or H-dependent witness data are selected here.
The result is a finite true E/F geometry, not merely a family
of sets, and uses no HKN theorem, recentering, abelianness, or
assumption s(1)=1.

Combining this fixed base with the factorial auxiliary action and
the selected relative effective H-lift is the next theorem. The
fixed raw-colour cover and coherent groupoid assembly are separate.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v}
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

namespace EffectiveGeometry

/-- Every finite, same-class-normalized old effective geometry with
a good raw effective colour admits ONE fixed finite factorial padded
constant-skeleton gauge, with a fixed literal old E/F embedding.

The existential quantifiers precede all S/H choices: no part of
the resulting carrier, old injection, or gauge depends on them. -/
theorem exists_fixedGoodFactorialEffectiveBase
    (D : EffectiveGeometry d.s A)
    (hSame : ∀ x y : A, D.part x y → D.F x y = 1)
    (hGood : d.selfReverseEffective.Nonempty) :
    ∃ (j : A → Fin (coherentPaddingSize A))
      (P : IndexedGauge d.s A (Quotient D.part))
      (Q : IndexedGauge d.s
        (Quotient D.part × Fin (coherentPaddingSize A))
        (Quotient D.part)),
      Function.Injective j ∧
      (∀ x : A, P.label x = Quotient.mk D.part x) ∧
      (∀ i k : Quotient D.part,
        P.skeleton i k = Classical.choose hGood) ∧
      (∀ x : A, P.vertexGauge x (P.label x) = 1) ∧
      (∀ w : Quotient D.part × Fin (coherentPaddingSize A),
        Q.label w = w.1 ∧ Q.vertexGauge w w.1 = 1) ∧
      (∀ x y : A,
        Q.toEffectiveGeometry.part
          (P.fixedUniformPaddingOldMap j x)
          (P.fixedUniformPaddingOldMap j y) ↔
            D.part x y) ∧
      (∀ x y : A, ¬D.part x y →
        Q.toEffectiveGeometry.F
          (P.fixedUniformPaddingOldMap j x)
          (P.fixedUniformPaddingOldMap j y) = D.F x y) ∧
      Finite (Quotient D.part × Fin (coherentPaddingSize A)) := by
  classical
  letI : Fintype (Quotient D.part) := Fintype.ofFinite _
  letI : LinearOrder (Quotient D.part) :=
    LinearOrder.lift' (Fintype.equivFin (Quotient D.part))
      (Fintype.equivFin (Quotient D.part)).injective
  obtain ⟨j, hj⟩ := exists_fixedFactorialOldInjection A
  let g0 : G := Classical.choose hGood
  have hFix : d.s g0 = g0 :=
    d.selfReverseEffective_subset_fixed (Classical.choose_spec hGood)
  let P : IndexedGauge d.s A (Quotient D.part) :=
    D.constantQuotientIndexedGauge g0 hFix
  let Q : IndexedGauge d.s
      (Quotient D.part × Fin (coherentPaddingSize A))
      (Quotient D.part) :=
    P.fixedUniformPaddingGauge g0 hFix (coherentPaddingSize A) j
  have hLabel (x : A) :
      P.label x = Quotient.mk D.part x := rfl
  have hConst (i k : Quotient D.part) :
      P.skeleton i k = g0 := rfl
  have hDiag (x : A) : P.vertexGauge x (P.label x) = 1 := by
    exact D.constantQuotientIndexedGauge_diagonal_one
      hSame g0 hFix x
  refine ⟨j, P, Q, hj, hLabel, hConst, hDiag, ?_, ?_, ?_, ?_⟩
  · intro w
    exact ⟨rfl, P.fixedUniformPaddingGauge_diagonal
      g0 hFix (coherentPaddingSize A) j w⟩
  · intro x y
    have hPart : P.toEffectiveGeometry.part x y ↔ D.part x y := by
      change (P.label x = P.label y) ↔ D.part x y
      rw [hLabel x, hLabel y]
      exact ⟨Quotient.exact, Quotient.sound⟩
    exact (P.fixedUniformPaddingOldMap_part
      g0 hFix (coherentPaddingSize A) j x y).trans hPart
  · intro x y hxy
    have hxyP : P.label x ≠ P.label y := by
      intro heq
      rw [hLabel x, hLabel y] at heq
      exact hxy (Quotient.exact heq)
    calc
      Q.toEffectiveGeometry.F
          (P.fixedUniformPaddingOldMap j x)
          (P.fixedUniformPaddingOldMap j y) =
        P.toEffectiveGeometry.F x y :=
          P.fixedUniformPaddingOldMap_colour
            g0 hFix hConst (coherentPaddingSize A) j hj
            x y hxyP
      _ = D.F x y :=
        D.constantQuotientIndexedGauge_cross g0 hFix x y hxy
  · infer_instance

end EffectiveGeometry

end SemigenericEPPA
