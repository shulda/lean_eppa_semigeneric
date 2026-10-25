import SemigenericEPPA.Algebra.DLFFiniteFaithfulInvariantCarrier
import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import SemigenericEPPA.Structure.DLFOldPartCloneExtension
import Mathlib.Algebra.Group.End

/-!
# Restrict a genuine finite original raw automorphism group to an invariant core

The negative DLF proof extracts a finite subgroup H of the actual
automorphism group of an infinite original-language raw rectangle
M. A finite H-invariant vertex set F supports a finite induced
raw rectangle, on which the SAME H acts by a strict homomorphism.

A crucial point: the restriction need not be faithful on an arbitrary
F. Faithfulness is recovered if F was chosen by the certified
finite-invariant-faithful-carrier theorem, which gives an explicit
separation property.

This module makes the old action and original E/R_c relations
literal; it does not assume the ambient carrier M finite.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

namespace RawRectanglePresentation

/-- A finite set F preserved under H contains the inverse orbit
of every one of its points, hence membership in F is literally
invariant under each group element. -/
theorem invariantFinset_iff
    (H : Subgroup (Equiv.Perm V))
    (F : Finset V)
    (hF : ∀ h : H, ∀ x : V, x ∈ F → h.val x ∈ F)
    (h : H) (x : V) :
    h.val x ∈ F ↔ x ∈ F := by
  constructor
  · intro hx
    have hinv := hF h⁻¹ (h.val x) hx
    have hh : (h⁻¹).val (h.val x) = x := by
      change (h.val)⁻¹ (h.val x) = x
      exact (h.val).symm_apply_apply x
    exact hh ▸ hinv
  · exact hF h x

/-- The same actual subgroup H≤Perm(V) acts strictly on
the subtype of a finite H-invariant vertex set, without assuming
its original action was faithful on an arbitrary selected F. -/
noncomputable def finiteInvariantRawAction
    (H : Subgroup (Equiv.Perm V))
    (F : Finset V)
    (hF : ∀ h : H, ∀ x : V, x ∈ F → h.val x ∈ F) :
    H →* Equiv.Perm {x : V // x ∈ F} where
  toFun h := h.val.subtypePerm (invariantFinset_iff H F hF h)
  map_one' := by
    ext x
    rfl
  map_mul' h k := by
    ext x
    rfl

/-- Exact original-language E preservation by each permutation of
the induced finite core, provided H preserves the original raw
relation on the infinite ambient structure. -/
theorem finiteInvariantRawAction_part
    (M : RawRectanglePresentation d V)
    (H : Subgroup (Equiv.Perm V))
    (hAut : H ≤ M.fullRawAutGroup)
    (F : Finset V)
    (hF : ∀ h : H, ∀ x : V, x ∈ F → h.val x ∈ F)
    (h : H) (x y : {x : V // x ∈ F}) :
    (M.pullbackRaw Subtype.val).part
        ((M.finiteInvariantRawAction H F hF h) x)
        ((M.finiteInvariantRawAction H F hF h) y) ↔
      (M.pullbackRaw Subtype.val).part x y := by
  let hRaw : M.fullRawAutGroup := ⟨h.val, hAut h.property⟩
  change M.part (h.val x.val) (h.val y.val) ↔ M.part x.val y.val
  exact M.fullRawAutGroup_part hRaw x.val y.val

/-- Exact literal preservation of EVERY ordered raw R_c colour,
not only the effective G-colour, on the induced finite carrier. -/
theorem finiteInvariantRawAction_colour
    (M : RawRectanglePresentation d V)
    (H : Subgroup (Equiv.Perm V))
    (hAut : H ≤ M.fullRawAutGroup)
    (F : Finset V)
    (hF : ∀ h : H, ∀ x : V, x ∈ F → h.val x ∈ F)
    (h : H) (x y : {x : V // x ∈ F}) :
    (M.pullbackRaw Subtype.val).colour
        ((M.finiteInvariantRawAction H F hF h) x)
        ((M.finiteInvariantRawAction H F hF h) y) =
      (M.pullbackRaw Subtype.val).colour x y := by
  let hRaw : M.fullRawAutGroup := ⟨h.val, hAut h.property⟩
  change M.colour (h.val x.val) (h.val y.val) =
    M.colour x.val y.val
  exact M.fullRawAutGroup_colour hRaw x.val y.val

/-- If the invariant finite set separates all elements of H, its
exact induced original-language action is faithful. -/
theorem finiteInvariantRawAction_injective
    (H : Subgroup (Equiv.Perm V))
    (F : Finset V)
    (hF : ∀ h : H, ∀ x : V, x ∈ F → h.val x ∈ F)
    (hSep : ∀ h k : H,
      (∀ x : V, x ∈ F → h.val x = k.val x) → h = k) :
    Function.Injective (finiteInvariantRawAction H F hF) := by
  intro h k heq
  apply hSep h k
  intro x hx
  let z : {x : V // x ∈ F} := ⟨x, hx⟩
  have hz := congrArg
    (fun p : Equiv.Perm {x : V // x ∈ F} => (p z).val) heq
  change h.val x = k.val x at hz
  exact hz

end RawRectanglePresentation
end SemigenericEPPA
