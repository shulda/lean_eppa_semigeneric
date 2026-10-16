import AllThoseEPPA.EPPA

/-!
# Consumer check of the upstream exact-coherence API

This module imports only the *definitions* from AllThoseEPPA.EPPA.  In
particular, it does not invoke AllThoseEPPA's HKN witness theorems.

The mathematical target is one coherent assignment on the groupoid of
partial isomorphisms with exactly matching range and next domain; an
individual EPPA witness and a lift of one finite group are weaker data.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

/-- A consumer-level typecheck of the chosen upstream definitions. -/
theorem coherentEPPA_implies_EPPA
    {L : Language.{u}} {Γ : Type v} [Group Γ]
    (act : L.Action Γ)
    {V : Type w} {W : Type z}
    {A : Structure L V} {B : Structure L W}
    (ψ : Structure.Embedding act A B)
    (h : Structure.IsCoherentEPPAWitness act ψ) :
    Structure.IsEPPAWitness act ψ := by
  obtain ⟨e⟩ := h
  exact e.isEPPAWitness

end SemigenericEPPA
