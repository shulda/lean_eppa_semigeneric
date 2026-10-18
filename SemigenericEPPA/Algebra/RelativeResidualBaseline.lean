import SemigenericEPPA.Algebra.ResidualBaseline

/-!
# A reversal-compatible raw baseline extending prescribed old edges

The fixed-cover homomorphic group lift requires a SINGLE baseline b
whose values on the old-old cross pairs have been prescribed by the
canonical raw sections. A free baseline chosen only from an auxiliary
linear order need not have those old values.

Given an effective geometry D, additive residual coefficient group L,
affine shift t, and one old subset S of vertices with a prescribed
cross-edge residual reference old(x,y), assume old already reverses
correctly on S×S.

The verified finite baseline theorem supplies an arbitrary b0 with
the correct reversal on all cross-pairs. Replace b0 on the symmetric
domain S×S by old. Since both orientations of an unordered old-old
pair are prescribed together, the affine reversal condition remains
valid. This yields a globally correct baseline which agrees with
ALL prescribed old-old cross references literally.

No H-action, fixed-point criterion, raw code, or EPPA theorem is
assumed. This is the baseline-prescription step in the manuscript's
fixed-cover finite-group raw lift.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G]
variable {L : Type v} [AddCommGroup L]
variable {V : Type w}
variable {s : AffineAntiInvolution G}

/-- Extend compatible old-old residual references to one full
reversal-compatible baseline. Only the actual cross-E values are
relevant; within E the baseline remains an arbitrary dummy. -/
theorem exists_finiteResidualBaseline_extendingSubset
    [Finite V]
    (D : EffectiveGeometry s V)
    (t : G → L)
    (ht : ∀ g, t (s g) = t g)
    (S : Set V)
    (old : V → V → L)
    (hOld : ∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
      old y x = t (D.F x y) - old x y) :
    ∃ b : V → V → L,
      (∀ x y, ¬D.part x y →
        b y x = t (D.F x y) - b x y) ∧
      (∀ x y, x ∈ S → y ∈ S → ¬D.part x y →
        b x y = old x y) := by
  classical
  obtain ⟨base, _, hbase⟩ :=
    exists_finiteResidualBaseline D t ht
  let b : V → V → L := fun x y =>
    if x ∈ S ∧ y ∈ S then old x y else base x y
  refine ⟨b, ?_, ?_⟩
  · intro x y hxy
    by_cases hpair : x ∈ S ∧ y ∈ S
    · have hpair' : y ∈ S ∧ x ∈ S :=
        ⟨hpair.2, hpair.1⟩
      change (if y ∈ S ∧ x ∈ S then old y x else base y x) =
        t (D.F x y) -
          (if x ∈ S ∧ y ∈ S then old x y else base x y)
      rw [if_pos hpair', if_pos hpair]
      exact hOld x y hpair.1 hpair.2 hxy
    · have hpair' : ¬(y ∈ S ∧ x ∈ S) := by
        intro h
        exact hpair ⟨h.2, h.1⟩
      change (if y ∈ S ∧ x ∈ S then old y x else base y x) =
        t (D.F x y) -
          (if x ∈ S ∧ y ∈ S then old x y else base x y)
      rw [if_neg hpair', if_neg hpair]
      exact hbase x y hxy
  · intro x y hx hy hxy
    change (if x ∈ S ∧ y ∈ S then old x y else base x y) =
      old x y
    rw [if_pos ⟨hx,hy⟩]

end SemigenericEPPA
