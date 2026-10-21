import SemigenericEPPA.Structure.EffectiveGeometry
import Mathlib.Algebra.Group.End

/-!
# Restriction of an auxiliary H-action to the fixed old embedded image

The positive coherent construction fixes an effective witness B and
an injection old:A→B BEFORE selecting an induced substructure S⊆A
or any group H. After factorial replication, an arbitrary H-action
on S has a strictly homomorphic auxiliary extension tau on B which
need NOT preserve the ambient old effective F outside S.

We isolate the exact elementary interface needed by the relative
H-lift: the set old(S) is tau-invariant, the restricted E relation
is preserved, and every F-colour across DIFFERENT E-parts of old(S)
is preserved. These assertions follow from the literal extension
equation tau(h)(old x)=old(h x) for x∈S, together with preservation
of old E/F on S. No global old F-automorphism of A or B is assumed.

The set old(S) is the image of a fixed map; it is NOT silently
replaced by its E-saturation. The proof is valid for all groups H,
including noncommutative and non-finite ones.
-/

namespace SemigenericEPPA

universe u v w t q
variable {G : Type u} [Group G]
variable {A : Type v} {W : Type w}
variable {H : Type t} [Group H]
variable {s : AffineAntiInvolution G}

/-- The actual image of the induced old subset under the original
preselected embedding, without adding any outside E-class points. -/
def embeddedOldSubset (old : A → W) (S : Set A) : Set W :=
  Set.range (fun x : S => old x.val)

/-- A strict whole-carrier H-action extending the selected old
action preserves EXACTLY the image of S. No assumption about
ambient E or F is needed for this elementary set assertion. -/
theorem embeddedOldSubset_invariant
    (old : A → W) (S : Set A)
    (rho : H →* Equiv.Perm S)
    (tau : H →* Equiv.Perm W)
    (hOld : ∀ (h : H) (x : S),
      tau h (old x.val) = old (rho h x).val)
    (h : H) (w : W) :
    w ∈ embeddedOldSubset old S ↔
      tau h w ∈ embeddedOldSubset old S := by
  change (∃ x : S, old x.val = w) ↔
    (∃ x : S, old x.val = tau h w)
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨rho h x, ?_⟩
    calc
      old (rho h x).val = tau h (old x.val) := (hOld h x).symm
      _ = tau h w := congrArg (tau h) hx
  · rintro ⟨x, hx⟩
    refine ⟨rho h⁻¹ x, ?_⟩
    calc
      old (rho h⁻¹ x).val = tau h⁻¹ (old x.val) :=
        (hOld h⁻¹ x).symm
      _ = tau h⁻¹ (tau h w) := congrArg (tau h⁻¹) hx
      _ = w := by simp

/-- The SAME geometric E relation on the literal image of S is
preserved under the auxiliary permutation tau, even though tau
may not preserve the old E/F data globally outside the image. -/
theorem embeddedOldSubset_part_invariant
    (D : EffectiveGeometry s A)
    (B : EffectiveGeometry s W)
    (old : A → W) (S : Set A)
    (hEmbedPart : ∀ x y : A,
      B.part (old x) (old y) ↔ D.part x y)
    (rho : H →* Equiv.Perm S)
    (tau : H →* Equiv.Perm W)
    (hOld : ∀ (h : H) (x : S),
      tau h (old x.val) = old (rho h x).val)
    (hE : ∀ (h : H) (x y : S),
      D.part (rho h x).val (rho h y).val ↔
        D.part x.val y.val)
    (h : H)
    (x y : {w : W // w ∈ embeddedOldSubset old S}) :
    B.part (tau h x.val) (tau h y.val) ↔
      B.part x.val y.val := by
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  calc
    B.part (tau h x.val) (tau h y.val) ↔
      D.part (rho h a).val (rho h b).val := by
        rw [← ha, ← hb, hOld h a, hOld h b]
        exact hEmbedPart _ _
    _ ↔ D.part a.val b.val := hE h a b
    _ ↔ B.part x.val y.val := by
      rw [← ha, ← hb]
      exact (hEmbedPart a.val b.val).symm

/-- The auxiliary H-action preserves every effective old cross-E
colour ON the selected embedded substructure, with no requirement
on colours involving old vertices outside S.

This is exactly the colour-preservation hypothesis consumed by
the relative selected-old H-multiplier theorem. -/
theorem embeddedOldSubset_cross_invariant
    (D : EffectiveGeometry s A)
    (B : EffectiveGeometry s W)
    (old : A → W) (S : Set A)
    (hEmbedPart : ∀ x y : A,
      B.part (old x) (old y) ↔ D.part x y)
    (hEmbedColour : ∀ x y : A, ¬D.part x y →
      B.F (old x) (old y) = D.F x y)
    (rho : H →* Equiv.Perm S)
    (tau : H →* Equiv.Perm W)
    (hOld : ∀ (h : H) (x : S),
      tau h (old x.val) = old (rho h x).val)
    (hE : ∀ (h : H) (x y : S),
      D.part (rho h x).val (rho h y).val ↔
        D.part x.val y.val)
    (hF : ∀ (h : H) (x y : S),
      ¬D.part x.val y.val →
      D.F (rho h x).val (rho h y).val = D.F x.val y.val)
    (h : H)
    (x y : {w : W // w ∈ embeddedOldSubset old S})
    (hxy : ¬B.part x.val y.val) :
    B.F (tau h x.val) (tau h y.val) = B.F x.val y.val := by
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  have hCross : ¬D.part a.val b.val := by
    intro hab
    apply hxy
    rw [← ha, ← hb]
    exact (hEmbedPart a.val b.val).mpr hab
  have hCross' : ¬D.part (rho h a).val (rho h b).val := by
    intro hab
    exact hCross ((hE h a b).mp hab)
  calc
    B.F (tau h x.val) (tau h y.val) =
        B.F (old (rho h a).val) (old (rho h b).val) := by
          rw [← ha, ← hb, hOld h a, hOld h b]
    _ = D.F (rho h a).val (rho h b).val :=
      hEmbedColour _ _ hCross'
    _ = D.F a.val b.val := hF h a b hCross
    _ = B.F (old a.val) (old b.val) :=
      (hEmbedColour _ _ hCross).symm
    _ = B.F x.val y.val := congrArg₂ B.F ha hb

end SemigenericEPPA
