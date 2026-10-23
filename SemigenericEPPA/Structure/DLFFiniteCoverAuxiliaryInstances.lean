import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import SemigenericEPPA.Algebra.RelativeDLFGraphFreeAction
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Basic.Finite.Prod
import Mathlib.Order.Basic

/-!
# Auxiliary finiteness and order instances for the DLF finite graph

The relative finite group cover uses graph vertices Q/H ⊕ (Bool × Q)
and edges Q ⊕ (Q × Q). The parity proof requires a linear order
only to choose orbit representatives. Neither order belongs to
the original R1--R3 relational language, nor is it a mathematical
restriction on the finite group Q and its subgroup H.

These low-priority instances choose orders on both finite carriers,
and expose finiteness of the *actual* raw automorphism group of
a finite rectangle presentation for downstream typeclass synthesis.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {V : Type w} {d : RawDatum G C}

/-- The full original-language automorphism group of a finite raw
rectangle is finite, as proved in the canonical full-Aut API. -/
instance finiteFullRawAutGroup
    (P : RawRectanglePresentation d V) [Finite V] :
    Finite P.fullRawAutGroup :=
  P.finite_fullRawAutGroup

namespace RelativeDLF

variable {Q : Type u} [Group Q] [Finite Q]

/-- An auxiliary enumeration of Q/H and the two regular vertex layers. -/
noncomputable instance (priority := 100) coverVertexFintypeOfFinite
    (H : Subgroup Q) : Fintype (CoverVertex H) := by
  classical
  haveI : Finite (LeftCosets H) := Quotient.finite _
  haveI : Finite (CoverVertex H) := by
    dsimp [CoverVertex]
    infer_instance
  exact Fintype.ofFinite _

/-- A chosen linear order on a finite graph vertex carrier, used
only for the involution-parity selector. -/
noncomputable instance (priority := 100) coverVertexLinearOrderOfFinite
    (H : Subgroup Q) : LinearOrder (CoverVertex H) :=
  LinearOrder.lift'
    (Fintype.equivFin (CoverVertex H))
    (Fintype.equivFin (CoverVertex H)).injective

/-- Edge carrier independent of H: one edge for q and one for (q,r). -/
noncomputable instance (priority := 100) coverEdgeFintypeOfFinite :
    Fintype (Q ⊕ (Q × Q)) := by
  classical
  haveI : Finite (Q ⊕ (Q × Q)) := inferInstance
  exact Fintype.ofFinite _

/-- The edge order is likewise auxiliary and not part of the language. -/
noncomputable instance (priority := 100) coverEdgeLinearOrderOfFinite :
    LinearOrder (Q ⊕ (Q × Q)) :=
  LinearOrder.lift'
    (Fintype.equivFin (Q ⊕ (Q × Q)))
    (Fintype.equivFin (Q ⊕ (Q × Q))).injective

end RelativeDLF
end SemigenericEPPA
