import SemigenericEPPA.Structure.SubsingletonFixedPartGeometry
import SemigenericEPPA.Valuations.UniformFibrePermutation
import SemigenericEPPA.Valuations.PartialPartPermutation

/-!
# Ordinary effective EPPA on the very same factorial-padded carrier

The earlier ordinary effective EPPA theorem uses a two-layer valuation
witness with common fibre V. For the coherent-positive G=1 branch
we instead need a larger, preselected carrier
    (V/E) × Fin M
with M divisible by all possible later occupied class sizes.

When G is subsingleton the effective colours are automatic and the
only partial-isomorphism data to extend is the E relation. Given a
fixed injection j:V↪Fin M, each old vertex sits at ([x],j x).
Every injective partial old E-isomorphism extends to a permutation
of this SAME carrier by:
  1. extending its partial E-class permutation on V/E;
  2. extending its partial fibre injection on each uniform Fin M.
Both gates are already Lean-verified; the present theorem applies
them to the literal fixed old embedding and certifies E/F preservation.

The witness is independent of the partial automorphism; M may be
chosen as |V|! BEFORE any later S or H.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Subsingleton G]
variable {V : Type v} {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Every partial effective E-isomorphism extends on ONE prescribed
equal-size padded carrier whose old embedding is fixed in advance.
No bound on M beyond existence of the old injection is needed. -/
theorem exists_subsingletonFixedPartPartialExtension
    [Finite V] (D : EffectiveGeometry s V)
    (M : ℕ) (j : V → Fin M) (hj : Function.Injective j)
    (S : Set V) (p : S → V)
    (hp : Function.Injective p)
    (hE : ∀ x y : S, D.part x.val y.val ↔
      D.part (p x) (p y)) :
    ∃ π : Equiv.Perm (Quotient D.part × Fin M),
      (∀ x : S,
        π (fixedSubsingletonOldMap D M j x.val) =
          fixedSubsingletonOldMap D M j (p x)) ∧
      (∀ x y : Quotient D.part × Fin M,
        (subsingletonFixedPartGeometry s (Quotient D.part) M).part
            (π x) (π y) ↔
          (subsingletonFixedPartGeometry s (Quotient D.part) M).part x y) ∧
      (∀ x y : Quotient D.part × Fin M,
        ¬(subsingletonFixedPartGeometry s (Quotient D.part) M).part x y →
        (subsingletonFixedPartGeometry s (Quotient D.part) M).F
          (π x) (π y) =
        (subsingletonFixedPartGeometry s (Quotient D.part) M).F
          x y) := by
  classical
  obtain ⟨ι, hι⟩ := D.exists_partPermutation_extending S p hE
  let old : V → Quotient D.part × Fin M :=
    fixedSubsingletonOldMap D M j
  have holdInj : Function.Injective old :=
    fixedSubsingletonOldMap_injective D M j hj
  -- The literal image of the partial old domain under the fixed old
  -- embedding; the inverse is picked only for this partial map.
  let T : Set (Quotient D.part × Fin M) :=
    Set.range (fun x : S => old x.val)
  let rep (z : T) : S := Classical.choose z.property
  have hrep (z : T) : old (rep z).val = z.val :=
    Classical.choose_spec z.property
  let q : T → Quotient D.part × Fin M :=
    fun z => old (p (rep z))
  have hqinj : Function.Injective q := by
    intro z w hzw
    have he : p (rep z) = p (rep w) := holdInj hzw
    have hrepEq : rep z = rep w :=
      Subtype.ext (hp he)
    apply Subtype.ext
    calc
      z.val = old (rep z).val := (hrep z).symm
      _ = old (rep w).val := congrArg (fun x : S => old x.val) hrepEq
      _ = w.val := hrep w
  have hqpart (z : T) : (q z).1 = ι z.val.1 := by
    calc
      (q z).1 = Quotient.mk D.part (p (rep z)) := rfl
      _ = ι (Quotient.mk D.part (rep z).val) := (hι (rep z)).symm
      _ = ι z.val.1 := by
        have hz : Quotient.mk D.part (rep z).val = z.val.1 :=
          congrArg Prod.fst (hrep z)
        exact congrArg ι hz
  obtain ⟨π, hπpart, hπext⟩ :=
    exists_uniformFibrePermutation_extending T q hqinj ι hqpart
  refine ⟨π, ?_, ?_, ?_⟩
  · intro x
    let z : T := ⟨old x.val, ⟨x, rfl⟩⟩
    have hz : rep z = x := by
      apply Subtype.ext
      exact holdInj (hrep z)
    have h := hπext z
    change π (old x.val) = old (p (rep z)) at h
    rw [hz] at h
    exact h
  · intro x y
    change (π x).1 = (π y).1 ↔ x.1 = y.1
    rw [hπpart x, hπpart y]
    exact ⟨fun h => ι.injective h, fun h => congrArg ι h⟩
  · intro x y hxy
    exact Subsingleton.elim _ _

end EffectiveGeometry

end SemigenericEPPA
