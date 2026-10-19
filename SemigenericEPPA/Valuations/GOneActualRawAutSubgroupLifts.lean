import SemigenericEPPA.Valuations.GOneJointRawLifts
import SemigenericEPPA.Bridge.BinaryRawAutomorphismSubgroup
import SemigenericEPPA.Bridge.ExactRawPartialGroupoid

/-!
# Genuine raw automorphism-subgroup extensions of all old arrows

The unconditional G=1 joint raw witness theorem provides ordinary
partial extension permutations and homomorphic H-group lifts on one
and the same raw-cover carrier W. The associated predicates are
the LITERAL old E relation and all raw P_c relations, not merely
the effective group colour.

For the coherent groupoid normal form, it is essential that every
connector extension and stabilizer-group lift land in the SAME group,
rather than just among uncertified permutations. Convert both
extension modes into the certified subgroup
  Aut_raw(W) ≤ Equiv.Perm W
from BinaryRawAutomorphismSubgroup.

This theorem makes explicit the group-valued data needed for the
final groupoid construction, without choosing representatives,
connectors or asserting coherent EPPA yet.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w t
variable {G : Type u} [Group G] [Subsingleton G] [Finite G]
variable {C : Type v} [Finite C]
variable {A : Type w} [Fintype A]
variable {d : RawDatum G C}

/-- The actual fixed raw cover Q on the factorial witness base. -/
noncomputable def RawRectanglePresentation.gOneJointRawPresentation
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover.{u, v, w, w, t}
      P P.gOneFactorialGeometry (P.gOneFactorialOldMap j)) :
    RawRectanglePresentation d (GOneJointRawCarrier P) :=
  rawCoverPresentation P.gOneFactorialGeometry
    K.code K.baseline K.baseline_reverse

/-- The literal raw-structure automorphism subgroup of Q. -/
abbrev RawRectanglePresentation.gOneJointRawAutGroup
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover.{u, v, w, w, t}
      P P.gOneFactorialGeometry (P.gOneFactorialOldMap j)) :=
  (P.gOneJointRawPresentation j K).actualRawAutomorphismGroup

/-- One canonical original zero-section embedding in the
complete finite raw witness carrier, independent of S,H. -/
def RawRectanglePresentation.gOneJointRawOldMap
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (x : A) : GOneJointRawCarrier P :=
  (P.gOneFactorialOldMap j x,
    fun _ : GOneFactorialCarrier P => (0 : UniversalResidualCarrier C))

/-- Actual raw partial isomorphisms have extensions INSIDE the
true automorphism subgroup of the SAME fixed full raw cover. -/
theorem RawRectanglePresentation.exists_gOneExactRawArrowExtension
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover.{u, v, w, w, t}
      P P.gOneFactorialGeometry (P.gOneFactorialOldMap j))
    (hPartial : P.HasAllJointRawPartialLifts j K)
    (S T : Set A)
    (f : ExactPartialIso P S T) :
    ∃ beta : P.gOneJointRawAutGroup j K,
      ∀ x : S,
        beta.val (P.gOneJointRawOldMap j x.val) =
          P.gOneJointRawOldMap j (f.toEquiv x).val := by
  let p : S → A := fun x => (f.toEquiv x).val
  have hp : Function.Injective p :=
    Subtype.val_injective.comp f.toEquiv.injective
  obtain ⟨perm, hOld, hPart, hRel⟩ :=
    hPartial S p hp
      (fun x y => (f.part_iff x y).symm)
      (fun x y => f.colour_eq x y)
  let Q := P.gOneJointRawPresentation j K
  have hPres : PreservesBinaryRawRelations Q.part
      (fun c x y => Q.colour x y = some c) perm := by
    refine ⟨?_, ?_⟩
    · intro X Y
      exact hPart X Y
    · intro c X Y
      change Q.colour (perm X) (perm Y) = some c ↔
        Q.colour X Y = some c
      exact hRel c X Y
  refine ⟨⟨perm, hPres⟩, ?_⟩
  intro x
  exact hOld x

/-- ANY H-action by raw automorphisms on ANY old induced S has
a genuine group-homomorphic lift into the SAME actual raw
automorphism subgroup, with literal extension on old vertices. -/
theorem RawRectanglePresentation.exists_gOneRawSubgroupLift
    (P : RawRectanglePresentation d A)
    (j : A → Fin (coherentPaddingSize A))
    (K : FixedJointRawCover.{u, v, w, w, t}
      P P.gOneFactorialGeometry (P.gOneFactorialOldMap j))
    (hGroups : P.HasAllJointRawGroupLifts j K)
    (H : Type t) [Group H]
    (S : Set A) (rho : H →* Equiv.Perm S)
    (hE : ∀ h : H, ∀ x y : S,
      P.part x.val y.val ↔
        P.part (rho h x).val (rho h y).val)
    (hRaw : ∀ h : H, ∀ x y : S,
      P.colour (rho h x).val (rho h y).val =
        P.colour x.val y.val) :
    ∃ lift : H →* P.gOneJointRawAutGroup j K,
      ∀ h : H, ∀ x : S,
        (lift h).val (P.gOneJointRawOldMap j x.val) =
          P.gOneJointRawOldMap j (rho h x).val := by
  obtain ⟨perm, hOld, hPart, hRel⟩ :=
    hGroups H S rho hE hRaw
  let Q := P.gOneJointRawPresentation j K
  have hPres : ∀ h : H, PreservesBinaryRawRelations Q.part
      (fun c x y => Q.colour x y = some c) (perm h) := by
    intro h
    refine ⟨?_, ?_⟩
    · intro X Y
      exact hPart h X Y
    · intro c X Y
      change Q.colour (perm h X) (perm h Y) = some c ↔
        Q.colour X Y = some c
      exact hRel h c X Y
  refine ⟨binaryRawAutHom Q.part
    (fun c x y => Q.colour x y = some c) perm hPres, ?_⟩
  intro h x
  exact hOld h x

end SemigenericEPPA
