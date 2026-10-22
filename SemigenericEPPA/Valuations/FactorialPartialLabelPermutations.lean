import SemigenericEPPA.Valuations.FactorialSelectedOldEFAction
import SemigenericEPPA.Valuations.UniformFibrePermutation

/-!
# Every old partial E-isomorphism extends on the SAME factorial carrier

The fixed nontrivial-G coherent construction uses a single auxiliary
old-label carrier W=(A/E)×Fin(|A|!), with one old injection j fixed
BEFORE all partial maps, subgroups and groupoid connectors.

To extend individual raw connectors on the SAME subsequent valuation
witness, first extend any injective old partial E-map p:S→A to a
genuine full auxiliary permutation pi of this exact W, together
with the induced class permutation iota.

This follows from the certified partial quotient E-permutation and
the general uniform-fibre partial-injection extension. It does NOT
assume p acts on all of A, or demand F invariance of pi outside S,
or replace j, the factorial carrier, or the old E-quotient.

This closes the literal real/index permutation gate for individual
connectors; fixed-skeleton partial gauge multipliers and the actual
full valuation automorphism remain separate.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] {A : Type v} [Fintype A]
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- One fixed factorial old injection suffices for EVERY exact
partial old E-isomorphism, including empty S and unequal original
E-class sizes: construct a compatible pair of actual full
permutations on the original imaginary part sort and the SAME
fixed auxiliary padded old-label carrier. -/
theorem exists_factorialPartialLabelPermutations
    (D : EffectiveGeometry s A)
    (j : A → Fin (coherentPaddingSize A))
    (hj : Function.Injective j)
    (S : Set A) (p : S → A)
    (hp : Function.Injective p)
    (hE : ∀ x y : S,
      D.part x.val y.val ↔ D.part (p x) (p y)) :
    ∃ (iota : Equiv.Perm (Quotient D.part))
      (pi : Equiv.Perm
        (Quotient D.part × Fin (coherentPaddingSize A))),
      (∀ z : Quotient D.part × Fin (coherentPaddingSize A),
        (pi z).1 = iota z.1) ∧
      (∀ x : S,
        pi (D.factorialAuxiliaryOldMap j x.val) =
          D.factorialAuxiliaryOldMap j (p x)) := by
  classical
  obtain ⟨iota, hiota⟩ := D.exists_partPermutation_extending S p hE
  let W : Type _ := Quotient D.part × Fin (coherentPaddingSize A)
  let old : A → W := D.factorialAuxiliaryOldMap j
  let oldS : S → W := fun x => old x.val
  have hOldInj : Function.Injective oldS := by
    intro x y hxy
    apply Subtype.ext
    exact hj (congrArg Prod.snd hxy)
  let selected : Set W := Set.range oldS
  let pp : selected → W :=
    fun z => old (p (Classical.choose z.property))
  have hChoose (x : S) :
      Classical.choose (show ∃ y : S, oldS y = oldS x
        from ⟨x, rfl⟩) = x := by
    apply hOldInj
    exact Classical.choose_spec
      (show ∃ y : S, oldS y = oldS x from ⟨x, rfl⟩)
  have hPPInj : Function.Injective pp := by
    intro x y hxy
    have hpOld :
        p (Classical.choose x.property) =
          p (Classical.choose y.property) :=
      hj (congrArg Prod.snd hxy)
    have hs :
        Classical.choose x.property =
          Classical.choose y.property := hp hpOld
    apply Subtype.ext
    calc
      x.val = oldS (Classical.choose x.property) :=
        (Classical.choose_spec x.property).symm
      _ = oldS (Classical.choose y.property) := congrArg oldS hs
      _ = y.val := Classical.choose_spec y.property
  have hPPPart : ∀ z : selected, (pp z).1 = iota z.val.1 := by
    intro z
    let x : S := Classical.choose z.property
    have hz : oldS x = z.val := Classical.choose_spec z.property
    change (old (p x)).1 = iota z.val.1
    calc
      (old (p x)).1 = Quotient.mk D.part (p x) := rfl
      _ = iota (Quotient.mk D.part x.val) := (hiota x).symm
      _ = iota z.val.1 :=
        congrArg iota (congrArg Prod.fst hz)
  obtain ⟨pi, hPiPart, hPiOld⟩ :=
    exists_uniformFibrePermutation_extending selected pp hPPInj
      iota hPPPart
  refine ⟨iota, pi, hPiPart, ?_⟩
  intro x
  let z : selected := ⟨oldS x, ⟨x, rfl⟩⟩
  have hChoice : Classical.choose z.property = x := by
    exact hOldInj (Classical.choose_spec z.property)
  calc
    pi (old x.val) = pp z := hPiOld z
    _ = old (p x) := by
      change old (p (Classical.choose z.property)) = old (p x)
      rw [hChoice]

end EffectiveGeometry

end SemigenericEPPA
