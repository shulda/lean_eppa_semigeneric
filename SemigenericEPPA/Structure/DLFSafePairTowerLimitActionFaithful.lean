import SemigenericEPPA.Structure.DLFSafePairTowerLimitMulAction

/-!
# The faithful limit action of genuine finite safe automorphism groups

Our quotient colimit group acts on the quotient colimit of finite
raw structures via the strictly equivariant stage maps.

If a group-limit element fixes EVERY limit vertex, choose one
finite stage representing the element, then restrict to all old
vertices of that stage. The injective canonical old vertex
embedding forces its representative to be the IDENTITY finite
permutation, hence the original element is the identity in
the group colimit.

This is an honest faithful action on the limit carrier, not
merely an abstract locally finite group. The separate step of
preserving literal raw E/R_c relations then places it inside
the actual automorphism group of the limit presentation.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type w} [∀ n, Finite (V n)]

namespace FiniteSafeRawPairTower

/-- A group-limit element that fixes all genuine colimit vertices
is literally the identity in the group-limit group. -/
theorem limitAct_faithful
    (T : FiniteSafeRawPairTower d V)
    (g : T.GroupLimit)
    (hg : ∀ x : T.VertexLimit, T.limitAct g x = x) :
    g = 1 := by
  obtain ⟨n, h, hh⟩ :=
    DirectLimit.exists_eq_mk (f := T.groupTransition) g
  have hFix : ∀ x : V n, h.val.val x = x := by
    intro x
    have hz := hg (T.vertexOf n x)
    rw [hh] at hz
    change T.limitAct (T.groupOf n h) (T.vertexOf n x) =
      T.vertexOf n x at hz
    rw [T.limitAct_of] at hz
    exact T.vertexOf_injective n hz
  have hPerm : h.val.val = 1 := by
    ext x
    simpa only [Equiv.Perm.coe_one, id_eq] using hFix x
  have hOne : h = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hPerm
  calc
    g = T.groupOf n h := hh
    _ = T.groupOf n 1 := by rw [hOne]
    _ = 1 := (DirectLimit.one_def (f := T.groupTransition) n).symm

end FiniteSafeRawPairTower
end SemigenericEPPA
