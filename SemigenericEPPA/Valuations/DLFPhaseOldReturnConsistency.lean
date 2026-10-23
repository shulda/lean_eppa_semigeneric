import SemigenericEPPA.Valuations.RelativeRegularPhaseGroupAction

/-!
# Relative phase: RETURN consistency on a non-invariant old B-copy

In relative safe EPPA one starts with A⊆B but a finite group H
acts only on A. A factorial effective witness for B supports
an extended H-action, and regular phases are added only outside
the embedded A sector.

The distinguished phase-one copy of B is NOT invariant under H.
This is intentional! A group element moving any vertex outside
A returns it to phase one only if the element is the identity.
Consequently an H-translate of a prescribed B-directed cross
pair can return to another prescribed B pair only:
* under the identity, which automatically preserves raw colours;
* or when BOTH of its endpoints lie in A, where the original
  genuine raw H-action preserves colours.

This is the exact return-consistency hypothesis needed to
extend prescribed raw colours from a non-invariant old subset
to its H-orbit saturation, avoiding the false demand that H
preserve all old B colours before their extension.

No finiteness, raw extension witness, or DLF theorem is claimed.
-/

namespace SemigenericEPPA

universe u v w
variable {H : Type u} [Group H]
variable {V : Type v} {C : Type w}

/-- A distinguished phase-one copy of an arbitrary B⊆V. This
subset generally is NOT invariant under the relative H-action. -/
def relativePhaseOldCopy
    (B : Set V) : Set (V × H) :=
  {X | X.1 ∈ B ∧ X.2 = 1}

/-- A group element returning an outside-A vertex to the
designated phase-one copy of B must be the IDENTITY. This is
precisely where the regular phase action is used. -/
theorem relativePhaseAction_outsideReturn_forces_one
    (rho : H →* Equiv.Perm V)
    (A B : Set V)
    (hA : ∀ (h : H) (x : V),
      x ∈ A ↔ rho h x ∈ A)
    (h : H) (x : V) (hx : x ∉ A)
    (hReturn : relativePhaseAction rho A hA h (x, (1 : H)) ∈
      relativePhaseOldCopy (H := H) B) :
    h = 1 := by
  have hphase := hReturn.2
  simpa [relativePhaseAction, relativePhasePerm, hx] using hphase

/-- If the two phase-one B vertices of a prescribed ordered
pair return to phase-one B under the SAME h, the original raw
colour is preserved. Raw H-invariance is only required on A×A,
never on the rest of B or on a larger effective witness. -/
theorem relativePhaseAction_oldRaw_returnConsistency
    (rho : H →* Equiv.Perm V)
    (A B : Set V)
    (hA : ∀ (h : H) (x : V),
      x ∈ A ↔ rho h x ∈ A)
    (oldRaw : V → V → C)
    (hRawInvariant : ∀ (h : H) (x y : V),
      x ∈ A → y ∈ A →
      oldRaw (rho h x) (rho h y) = oldRaw x y)
    (h : H) (x y : V)
    (hReturnX : relativePhaseAction rho A hA h (x, (1 : H)) ∈
      relativePhaseOldCopy (H := H) B)
    (hReturnY : relativePhaseAction rho A hA h (y, (1 : H)) ∈
      relativePhaseOldCopy (H := H) B) :
    oldRaw (rho h x) (rho h y) = oldRaw x y := by
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · exact hRawInvariant h x y hx hy
    · have hOne :=
        relativePhaseAction_outsideReturn_forces_one
          rho A B hA h y hy hReturnY
      subst h
      simp
  · have hOne :=
      relativePhaseAction_outsideReturn_forces_one
        rho A B hA h x hx hReturnX
    subst h
    simp

/-- The exact equivalence at the individual vertex level:
for an outside-A vertex x, an H-translate of (x,1) can lie in
the designated B zero-section iff h=1 and x∈B. -/
theorem relativePhaseAction_outside_return_iff
    (rho : H →* Equiv.Perm V)
    (A B : Set V)
    (hA : ∀ (h : H) (x : V),
      x ∈ A ↔ rho h x ∈ A)
    (h : H) (x : V) (hx : x ∉ A) :
    relativePhaseAction rho A hA h (x, (1 : H)) ∈
        relativePhaseOldCopy (H := H) B ↔
      h = 1 ∧ x ∈ B := by
  constructor
  · intro hReturn
    have hOne :=
      relativePhaseAction_outsideReturn_forces_one
        rho A B hA h x hx hReturn
    subst h
    refine ⟨rfl, ?_⟩
    simpa [relativePhaseOldCopy] using hReturn
  · rintro ⟨rfl, hB⟩
    simpa [relativePhaseOldCopy, relativePhaseAction,
      relativePhasePerm] using
      (show (x, (1 : H)) ∈ relativePhaseOldCopy (H := H) B
        from ⟨hB, rfl⟩)

end SemigenericEPPA
