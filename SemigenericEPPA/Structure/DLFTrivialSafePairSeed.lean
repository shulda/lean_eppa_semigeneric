import SemigenericEPPA.Structure.DLFFiniteSafePairEmbeddings

/-!
# Every finite original raw rectangle has a trivially safe acting subgroup

The positive DLF tower construction must begin with an arbitrary
finite member A of the original age, whether or not the group datum
has any good colour. The subgroup {1} ≤ Aut_raw(A) is always
locally involution-safe: an identity action cannot reverse a pair
from distinct E-classes.

This provides an actual finite safe pair from any finite raw
presentation, avoiding an artificial initial-safety hypothesis.
Subsequent nontrivial finite subgroups are constructed by the
certified relative safe-group EPPA theorem under one good orbit.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G]
variable {C : Type v}
variable {V : Type w} [Finite V]
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Every finite genuine original R1–R3 raw presentation, with no
good-colour hypothesis, gives an ACTUAL finite safe pair whose
group is the trivial subgroup of its full raw automorphism group. -/
noncomputable def trivialSafePair
    (P : RawRectanglePresentation d V) :
    FiniteSafeRawPair d V where
  raw := P
  subgroup := ⊥
  safe := by
    intro h _ x y hcross hx _
    have hOne : h.val = 1 := Subgroup.mem_bot.mp h.property
    have hPerm : (h.val.val : Equiv.Perm V) = 1 :=
      congrArg Subtype.val hOne
    have hFix : h.val.val x = x := by
      rw [hPerm]
      rfl
    have hEq : x = y := hFix.symm.trans hx
    subst y
    exact False.elim (hcross (P.part_equiv.refl x))

end RawRectanglePresentation
end SemigenericEPPA
