import SemigenericEPPA.Algebra.EquivariantFibreMultiplicity
import SemigenericEPPA.Algebra.AssembledReplicatedFibreCoding
import Mathlib.Data.Fintype.Card

/-!
# Canonical class cardinalities do not depend on Fintype choices

The invariant class-fibre cardinal oldClassFibreCard is defined
noncomputably using classical finiteness. Downstream fixed-fibre
codings accept an *explicit* Fintype structure on each occupied
subtype. These may use different decidability algorithms and hence
are not definitionally equal in Lean, even though the underlying
finite type is the same.

Fintype.card_congr applied to the identity equivalence shows that
the numeric cardinalities coincide. This gives the exact bridge
needed to feed factorial divisibility theorems into the concrete
classwise replica coding.
-/

namespace SemigenericEPPA

universe u v
variable {S : Type u} [Fintype S] {I : Type v}

/-- The canonical numerical old-class cardinal is equal to the
cardinality obtained from any explicitly provided Fintype instance.
No definitional equality of the Fintype structures is required. -/
theorem oldClassFibreCard_eq_givenFintype
    (cls : S → I) (i : I)
    (hfin : Fintype (OldClassFibre cls i)) :
    oldClassFibreCard cls i =
      @Fintype.card (OldClassFibre cls i) hfin := by
  classical
  unfold oldClassFibreCard
  exact @Fintype.card_congr
    (OldClassFibre cls i) (OldClassFibre cls i)
      (Subtype.fintype (fun x : S => cls x = i)) hfin (Equiv.refl _)

/-- The same interface specialized to occupied E-class indices,
where class-fibre types are named ReplicatedOldFibre. -/
theorem occupiedOldClassFibreCard_eq
    (cls : S → I)
    (i : ReplicatedOccupiedIndex cls)
    (hfin : Fintype (ReplicatedOldFibre cls i)) :
    oldClassFibreCard cls i.val =
      @Fintype.card (ReplicatedOldFibre cls i) hfin :=
  oldClassFibreCard_eq_givenFintype cls i.val hfin

end SemigenericEPPA
