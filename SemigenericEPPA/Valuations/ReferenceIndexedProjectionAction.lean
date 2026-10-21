import SemigenericEPPA.Valuations.ReferenceIndexedOldSubsetLift
import SemigenericEPPA.Bridge.OccupiedProjectionFlipSafety

/-!
# The actual indexed valuation H-action preserves old-label projections

For the nontrivial-G positive coherent construction, the relative
H-action is the genuine two-layer coordinate permutation
referenceIndexedWitnessAction. It acts simultaneously on the
witness part q=(i,f), on an old padded real label x, and on a
valuation of target parts.

The already certified group-action constructor, not just its
existence statement, satisfies two EXACT equivariance identities:
  (Theta_h X).old = rho_h(X.old)
  (Theta_h X).part.1 = iota_h(X.part.1).

Consequently ANY H-equivariant partial projection from old padded
labels to genuine selected vertices S automatically lifts to an
H-equivariant Option-valued projection on all valuation vertices.

If the index action fixes unoccupied E-classes, a genuinely swapped
cross-witness pair with different original E-indices MUST lie in
occupied classes. This is exactly the geometric precondition of
the previously certified occupied-projection raw flip-safety
mechanism. It is independent of G being trivial.

No projection onto old S is invented here; the factorial replicated
coding is the separate construction that provides it.
-/

namespace SemigenericEPPA

universe u v w z
variable {H : Type u} [Group H]
variable {G : Type v} [Group G] {V : Type w}
variable {S : Type z}
variable {s : AffineAntiInvolution G}

namespace EffectiveGeometry

/-- Literal old-label coordinate of the ACTUAL relative indexed
H-action on the entire two-layer valuation witness. This identity
holds for arbitrary chosen reference twists and gauge multipliers
satisfying their strict group cocycle equations. -/
theorem referenceIndexedWitnessAction_oldLabel
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (h : H) (X : EffectiveWitnessVertex D) :
    (D.referenceIndexedWitnessAction rho iota z hcls
      M hOne hMul h X).old = rho h X.old := by
  change
    (witnessCocyclePerm D
      (referenceWitnessPartAction D rho iota z) rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      (fun k q r => M k q.1 r.1) h X).old = rho h X.old
  exact witnessCocyclePerm_old D
    (referenceWitnessPartAction D rho iota z) rho
    (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
    (fun k q r => M k q.1 r.1) h X

/-- Literal transformation of the ORIGINAL E-index component,
even though the larger witness-part valuation coordinate may
change under nontrivial reference twists. -/
theorem referenceIndexedWitnessAction_oldIndex
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (h : H) (X : EffectiveWitnessVertex D) :
    (D.referenceIndexedWitnessAction rho iota z hcls
      M hOne hMul h X).part.1 = iota h X.part.1 := by
  change
    (witnessCocyclePerm D
      (referenceWitnessPartAction D rho iota z) rho
      (referenceWitnessPartAction_fibre_compat D rho iota z hcls)
      (fun k q r => M k q.1 r.1) h X).part.1 =
        iota h X.part.1
  rw [witnessCocyclePerm_part]
  exact referenceWitnessPartAction_class D rho iota z h X.part

/-- Any genuinely H-equivariant Option-valued projection from the
old padded label sort lifts automatically to the whole valuation
witness. There is NO false projection from unoccupied indices:
none is retained on exactly those vertices. -/
theorem referenceIndexedWitnessAction_projection
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (rhoSelected : H →* Equiv.Perm S)
    (proj : V → Option S)
    (hproj : ∀ (h : H) (x : V),
      proj (rho h x) = Option.map (rhoSelected h) (proj x))
    (h : H) (X : EffectiveWitnessVertex D) :
    proj ((D.referenceIndexedWitnessAction rho iota z hcls
        M hOne hMul h X).old) =
      Option.map (rhoSelected h) (proj X.old) := by
  rw [D.referenceIndexedWitnessAction_oldLabel
    rho iota z hcls M hOne hMul h X]
  exact hproj h X.old

/-- A cross-pair genuinely exchanged by an element of the actual
relative valuation group action cannot involve an unoccupied
ORIGINAL E-index when the quotient action fixes such indices.

No restriction on the order of the swapping element, no condition
on the witness part-valuations and no assumption G=1. -/
theorem referenceIndexedWitnessAction_swapped_occupied
    (D : EffectiveGeometry s V)
    (rho : H →* Equiv.Perm V)
    (iota : H →* Equiv.Perm (Quotient D.part))
    (z : V → Quotient D.part → G)
    (hcls : ∀ (h : H) (x : V),
      Quotient.mk D.part (rho h x) =
        iota h (Quotient.mk D.part x))
    (M : H → Quotient D.part → Quotient D.part → G)
    (hOne : ∀ i j : Quotient D.part, M 1 i j = 1)
    (hMul : ∀ (k h : H) (i j : Quotient D.part),
      M (k * h) i j =
        M k (iota h i) (iota h j) * M h i j)
    (occupied : Quotient D.part → Prop)
    (hFixed : ∀ (h : H) (i : Quotient D.part),
      ¬occupied i → iota h i = i)
    (h : H) (X Y : EffectiveWitnessVertex D)
    (hCross : X.part.1 ≠ Y.part.1)
    (hSwap : D.referenceIndexedWitnessAction
      rho iota z hcls M hOne hMul h X = Y) :
    occupied X.part.1 ∧ occupied Y.part.1 := by
  let Theta : H →* Equiv.Perm (EffectiveWitnessVertex D) :=
    D.referenceIndexedWitnessAction rho iota z hcls M hOne hMul
  have hIdx (k : H) (W : EffectiveWitnessVertex D) :
      (Theta k W).part.1 = iota k W.part.1 :=
    D.referenceIndexedWitnessAction_oldIndex
      rho iota z hcls M hOne hMul k W
  exact flippedCrossPart_occupied
    (fun W : EffectiveWitnessVertex D => W.part.1)
    Theta iota occupied hIdx hFixed h X Y hCross hSwap

end EffectiveGeometry

end SemigenericEPPA
