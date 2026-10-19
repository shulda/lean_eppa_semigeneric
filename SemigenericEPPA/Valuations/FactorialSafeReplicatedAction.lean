import SemigenericEPPA.Valuations.SafeReplicatedFixedCarrierAction
import SemigenericEPPA.Algebra.FactorialOldFibreMultiplicities
import SemigenericEPPA.Algebra.OldClassFibreCardInstance

/-!
# Genuine safe H-action with one a priori factorial-sized fibre

The previous safe replicated-carrier group-lift theorem assumes a
multiplicity t_i for every E-class with strict H-invariance and
|S_i|*t_i=M on all occupied parts. All these arithmetic conditions
follow automatically from M=|A|! when the selected old carrier S
injects into the original finite carrier A.

This theorem performs the exact *typeclass-level* composition:
the canonical oldClassFibreCard from the arithmetic proof and the
explicit Fintype supplied to the fixed-fibre β_i coding need not be
definitionally the same enumeration, but their cardinalities agree.
We therefore obtain a genuine H→*Perm of the SAME prechosen carrier
I×Fin(|A|!), preserving E/F, all original old zero-copy vertices,
and raw flip-safety for any element of H.

No subgroup, induced substructure or automorphism is allowed to
change the fixed factorial carrier. The remaining task is to produce
the compatible class-index action and literal old colour data
directly from the original raw presentation.
-/

namespace SemigenericEPPA

universe u v w z t q

variable {H : Type u} [Group H]
variable {G : Type v} [Group G] [Subsingleton G]
variable {C : Type w} {S : Type z} [Fintype S]
variable {I : Type t} {A : Type q} [Fintype A]

/-- Every finite selected S injected into original A admits a safe,
strict H-action on ONE preselected factorial-padded effective base,
given only genuine old H/E and raw-colour invariance data. The
formerly abstract t_i and divisibility hypotheses are gone. -/
theorem exists_factorialSafeReplicatedFixedCarrierAction
    (d : RawDatum G C)
    (D : EffectiveGeometry d.s S)
    (B : EffectiveGeometry d.s
      (I × Fin (coherentPaddingSize A)))
    (inc : S → A) (hInc : Function.Injective inc)
    (cls : S → I)
    (hDpart : ∀ x y : S, D.part x y ↔ cls x = cls y)
    (hBpart : ∀ x y : I × Fin (coherentPaddingSize A),
      B.part x y ↔ x.1 = y.1)
    (old : S → S → C)
    (hPhi : ∀ x y : S, ¬D.part x y →
      d.phi (old x y) = D.F x y)
    (hReverse : ∀ x y : S, ¬D.part x y →
      old y x = d.reverse (old x y))
    (rho : H →* Equiv.Perm S)
    (iota : H →* Equiv.Perm I)
    (hCls : ∀ (h : H) (x : S),
      cls (rho h x) = iota h (cls x))
    (hFixed : ∀ (h : H) (i : I),
      (¬∃ x : S, cls x = i) → iota h i = i)
    (hRaw : ∀ (h : H) (x y : S), ¬D.part x y →
      old (rho h x) (rho h y) = old x y)
    (j : ∀ i : ReplicatedOccupiedIndex cls,
      ReplicatedOldFibre cls i → Fin (coherentPaddingSize A))
    (hj : ∀ i : ReplicatedOccupiedIndex cls,
      Function.Injective (j i)) :
    ∃ action : H →* Equiv.Perm (I × Fin (coherentPaddingSize A)),
      (∀ (h : H) (x : S),
        action h (fixedReplicaOldMap cls (coherentPaddingSize A) j x) =
          fixedReplicaOldMap cls (coherentPaddingSize A) j (rho h x)) ∧
      (∀ (h : H) (x : I × Fin (coherentPaddingSize A)),
        (action h x).1 = iota h x.1) ∧
      (∀ (h : H) (x y : I × Fin (coherentPaddingSize A)),
        B.part (action h x) (action h y) ↔ B.part x y) ∧
      (∀ (h : H) (x y : I × Fin (coherentPaddingSize A)),
        ¬B.part x y →
        B.F (action h x) (action h y) = B.F x y) ∧
      (∀ (h : H) (x y : I × Fin (coherentPaddingSize A)),
        ¬B.part x y → action h x = y → action h y = x →
        ∃ c : C, d.phi c = B.F x y ∧ d.reverse c = c) := by
  classical
  let t : I → ℕ := oldClassFibreMultiplicity cls (coherentPaddingSize A)
  obtain ⟨hpos, hsize, ht⟩ :=
    factorialOldFibreMultiplicity_laws inc hInc cls rho iota hCls
  let hfin (i : ReplicatedOccupiedIndex cls) :
      Fintype (ReplicatedOldFibre cls i) := by
    classical
    infer_instance
  have hsizeExplicit (i : ReplicatedOccupiedIndex cls) :
      (@Fintype.card (ReplicatedOldFibre cls i) (hfin i)) * t i.val =
        coherentPaddingSize A := by
    have h := hsize i
    rw [occupiedOldClassFibreCard_eq cls i (hfin i)] at h
    exact h
  exact exists_safeReplicatedFixedCarrierAction
    d D (coherentPaddingSize A) B cls hDpart hBpart old
      hPhi hReverse rho iota hCls hFixed hRaw
      t ht hfin hpos hsizeExplicit j hj

end SemigenericEPPA
