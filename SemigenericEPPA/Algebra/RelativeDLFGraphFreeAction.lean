import SemigenericEPPA.Algebra.RelativeDLFLeftCosetAction
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Group

/-!
# Relative DLF finite cover: three vertex layers and two edge layers

Given Q and H≤Q, the audited involution-killing construction uses
the graph with vertex layers
  X0 = Q/H,   X1 = Q×{false},   X2 = Q×{true},
and edge layers
  E0 = Q (connecting qH to (false,q)),
  E1 = Q×Q (connecting (false,q) to (true,r)).
Q acts by left translation on all Q coordinates and on Q/H.

Every edge has its endpoints in DIFFERENT Q-invariant layers, so
the Q-action NEVER inverts an undirected edge. All edge sets have
free Q-action by left translation on an explicit Q coordinate.
An element not conjugate into H has no fixed vertices even in
the coset layer; no nonidentity group element fixes any edge.

We do not claim the parity obstruction or build the semidirect
edge-chain cover yet. This module supplies the exact finite
graph-action axioms needed for the next step.
-/

namespace SemigenericEPPA

universe u
variable {Q : Type u} [Group Q]

namespace RelativeDLF

/-- The coset, free-first and free-second vertex layers. -/
abbrev CoverVertex (H : Subgroup Q) :=
  LeftCosets H ⊕ (Bool × Q)

/-- One coset-to-first-layer edge per q and one first-to-second
edge per ordered pair q,r. No loops or parallel edge collapse. -/
abbrev CoverEdge (_H : Subgroup Q) :=
  Q ⊕ (Q × Q)

def edgeSource (H : Subgroup Q) :
    CoverEdge H → CoverVertex H
  | .inl q => .inl (Quotient.mk (leftCosetSetoid H) q)
  | .inr (q, _) => .inr (false, q)

def edgeTarget (H : Subgroup Q) :
    CoverEdge H → CoverVertex H
  | .inl q => .inr (false, q)
  | .inr (_, r) => .inr (true, r)

/-- Actual left-regular permutation of the group Q. -/
def regularLeftPerm (g : Q) : Equiv.Perm Q where
  toFun q := g * q
  invFun q := g⁻¹ * q
  left_inv := by intro q; group
  right_inv := by intro q; group

@[simp] theorem regularLeftPerm_apply (g q : Q) :
    regularLeftPerm g q = g * q := rfl

def vertexPerm (H : Subgroup Q) (g : Q) :
    Equiv.Perm (CoverVertex H) :=
  Equiv.sumCongr (leftCosetPerm H g)
    (Equiv.prodCongr (Equiv.refl Bool) (regularLeftPerm g))

def edgePerm (H : Subgroup Q) (g : Q) :
    Equiv.Perm (CoverEdge H) :=
  Equiv.sumCongr (regularLeftPerm g)
    (Equiv.prodCongr (regularLeftPerm g) (regularLeftPerm g))

@[simp] theorem vertexPerm_coset (H : Subgroup Q)
    (g : Q) (x : LeftCosets H) :
    vertexPerm H g (.inl x) = .inl (leftCosetAction H g x) := rfl

@[simp] theorem vertexPerm_free (H : Subgroup Q)
    (g : Q) (layer : Bool) (q : Q) :
    vertexPerm H g (.inr (layer, q)) = .inr (layer, g * q) := rfl

@[simp] theorem edgePerm_cosetEdge (H : Subgroup Q)
    (g q : Q) :
    edgePerm H g (.inl q) = .inl (g * q) := rfl

@[simp] theorem edgePerm_crossEdge (H : Subgroup Q)
    (g q r : Q) :
    edgePerm H g (.inr (q,r)) = .inr (g * q,g * r) := rfl

/-- Strict Q-action on all three vertex layers. -/
def vertexAction (H : Subgroup Q) :
    Q →* Equiv.Perm (CoverVertex H) where
  toFun := vertexPerm H
  map_one' := by
    apply Equiv.ext
    intro x
    cases x with
    | inl x =>
        simpa [vertexPerm, leftCosetPerm] using
          (leftCosetTranslate_one H x)
    | inr y =>
        rcases y with ⟨layer, q⟩
        simp
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro x
    cases x with
    | inl x =>
        change Sum.inl (leftCosetAction H (g * h) x) =
          Sum.inl (leftCosetAction H g (leftCosetAction H h x))
        rw [map_mul]
        rfl
    | inr y =>
        rcases y with ⟨layer, q⟩
        simp [mul_assoc]

/-- Strict Q-action on the two edge layers. -/
def edgeAction (H : Subgroup Q) :
    Q →* Equiv.Perm (CoverEdge H) where
  toFun := edgePerm H
  map_one' := by
    apply Equiv.ext
    intro e
    cases e with
    | inl q => simp
    | inr qr => rcases qr with ⟨q,r⟩; simp
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro e
    cases e with
    | inl q => simp [mul_assoc]
    | inr qr => rcases qr with ⟨q,r⟩; simp [mul_assoc]

/-- Source and target are genuinely equivariant; the coset
representative q and the free coordinate always move together. -/
theorem edgeSource_equivariant (H : Subgroup Q)
    (g : Q) (e : CoverEdge H) :
    edgeSource H (edgePerm H g e) =
      vertexPerm H g (edgeSource H e) := by
  cases e with
  | inl q =>
      simpa [edgeSource, edgePerm, vertexPerm, leftCosetPerm] using
        (leftCosetTranslate_mk H g q).symm
  | inr qr => rcases qr with ⟨q,r⟩; simp [edgeSource]

theorem edgeTarget_equivariant (H : Subgroup Q)
    (g : Q) (e : CoverEdge H) :
    edgeTarget H (edgePerm H g e) =
      vertexPerm H g (edgeTarget H e) := by
  cases e with
  | inl q => simp [edgeTarget]
  | inr qr => rcases qr with ⟨q,r⟩; simp [edgeTarget]

/-- Every edge connects two distinct invariant layers, so not even
an involution can exchange its endpoints. -/
theorem no_edge_inversion (H : Subgroup Q)
    (g : Q) (e : CoverEdge H) :
    ¬(vertexPerm H g (edgeSource H e) = edgeTarget H e ∧
        vertexPerm H g (edgeTarget H e) = edgeSource H e) := by
  cases e with
  | inl q =>
      intro h
      cases h.1
  | inr qr =>
      rcases qr with ⟨q,r⟩
      intro h
      have heq := h.1
      simp [edgeSource, edgeTarget] at heq

/-- Every nonidentity group element acts without fixed EDGES,
independently of the conjugacy condition on H. -/
theorem edgeAction_free_of_ne_one (H : Subgroup Q)
    (g : Q) (hg : g ≠ 1) (e : CoverEdge H) :
    edgePerm H g e ≠ e := by
  cases e with
  | inl q =>
      intro heq
      have hq : g * q = q := Sum.inl.inj heq
      apply hg
      have heq : g * q = (1 : Q) * q := by
        simpa only [one_mul] using hq
      exact mul_right_cancel heq
  | inr qr =>
      rcases qr with ⟨q,r⟩
      intro heq
      have hq : g * q = q :=
        congrArg Prod.fst (Sum.inr.inj heq)
      apply hg
      have heq : g * q = (1 : Q) * q := by
        simpa only [one_mul] using hq
      exact mul_right_cancel heq

/-- An element not conjugate into H fixes no vertex in ANY layer.
The coset layer uses the exact nonnormal coset-stabilizer lemma,
while both regular layers are free under left multiplication. -/
theorem vertexAction_free_of_no_conjugate
    (H : Subgroup Q) (g : Q)
    (hBad : ∀ q : Q, q⁻¹ * g * q ∉ H)
    (x : CoverVertex H) :
    vertexPerm H g x ≠ x := by
  have hg : g ≠ 1 := by
    intro heq
    exact hBad 1 (by simp [heq])
  cases x with
  | inl x =>
      intro heq
      exact leftCosetAction_no_fixed_of_no_conjugate H g hBad x
        (Sum.inl.inj heq)
  | inr pair =>
      rcases pair with ⟨layer,q⟩
      intro heq
      have hq : g * q = q :=
        congrArg Prod.snd (Sum.inr.inj heq)
      apply hg
      have heq : g * q = (1 : Q) * q := by
        simpa only [one_mul] using hq
      exact mul_right_cancel heq

end RelativeDLF

end SemigenericEPPA
