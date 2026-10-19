import SemigenericEPPA.Bridge.CoherentAllRawComponents

/-!
# Flatten coherent component-indexed groupoid extensions to ALL exact arrows

One actual raw partial isomorphism f:S→T forces S and T to lie
in the SAME old raw-isomorphism component q. A previously selected
family of coherent extension functors Phi_q can therefore be
evaluated on f by choosing q to be the quotient class of S and
casting T to an object of that same component.

No extra choices are made at the arrow level, and the target
component proof is proposition-valued. We prove the result is
independent of any alternative but equal component index, so
identity, composition and original-old-vertex extension are inherited
from the componentwise formulas literally.

This is the final exact-groupoid INDEXING step. Converting the
result to upstream typed CoherentExtension and producing the
unconditional G=1 component functors are separate steps.
-/

namespace SemigenericEPPA

universe u v w t

variable {G : Type u} [Group G] {C : Type v}
variable {A : Type w} {W : Type t}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Any exact old raw arrow identifies the quotient isomorphism
classes of its source and target subsets. -/
theorem exactRawArrow_component_eq
    (P : RawRectanglePresentation d A)
    (S T : Set A)
    (f : ExactPartialIso P S T) :
    Quotient.mk P.rawIsoSetoid T =
      Quotient.mk P.rawIsoSetoid S :=
  Quotient.sound ⟨f.symm⟩

/-- Evaluate the prechosen q-component functor at an exact arrow
S→T, using the canonical component of S. -/
noncomputable def flattenCoherentRawComponents
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (Phi : (q : RawIsoComponent P) →
      (i j : RawComponentObject P q) →
        ExactPartialIso P i.val j.val → K)
    (S T : Set A)
    (f : ExactPartialIso P S T) : K :=
  let q : RawIsoComponent P := Quotient.mk P.rawIsoSetoid S
  let i : RawComponentObject P q := ⟨S, rfl⟩
  let j : RawComponentObject P q :=
    ⟨T, P.exactRawArrow_component_eq S T f⟩
  Phi q i j f

/-- The flattened value agrees with evaluation at ANY common
component q of both source and target. This is proved by
equality induction; any differences of subtype proof fields
are irrelevant. -/
theorem flattenCoherentRawComponents_at
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (Phi : (q : RawIsoComponent P) →
      (i j : RawComponentObject P q) →
        ExactPartialIso P i.val j.val → K)
    (S T : Set A) (f : ExactPartialIso P S T)
    (q : RawIsoComponent P)
    (hs : Quotient.mk P.rawIsoSetoid S = q)
    (ht : Quotient.mk P.rawIsoSetoid T = q) :
    P.flattenCoherentRawComponents K Phi S T f =
      Phi q ⟨S, hs⟩ ⟨T, ht⟩ f := by
  cases hs
  rfl

/-- Componentwise identity is exactly a global groupoid identity. -/
theorem flattenCoherentRawComponents_id
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (Phi : (q : RawIsoComponent P) →
      (i j : RawComponentObject P q) →
        ExactPartialIso P i.val j.val → K)
    (hId : ∀ (q : RawIsoComponent P)
      (i : RawComponentObject P q),
      Phi q i i (ExactPartialIso.refl P i.val) = 1)
    (S : Set A) :
    P.flattenCoherentRawComponents K Phi S S
      (ExactPartialIso.refl P S) = 1 := by
  have h := P.flattenCoherentRawComponents_at K Phi
    S S (ExactPartialIso.refl P S)
    (Quotient.mk P.rawIsoSetoid S) rfl rfl
  rw [h]
  exact hId (Quotient.mk P.rawIsoSetoid S) ⟨S, rfl⟩

/-- Exact domain/range-matched composition is strictly preserved
globally, even when f and g are originally indexed by different
but equal quotient representatives. -/
theorem flattenCoherentRawComponents_comp
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (Phi : (q : RawIsoComponent P) →
      (i j : RawComponentObject P q) →
        ExactPartialIso P i.val j.val → K)
    (hComp : ∀ (q : RawIsoComponent P)
      (i j k : RawComponentObject P q)
      (f : ExactPartialIso P i.val j.val)
      (g : ExactPartialIso P j.val k.val),
      Phi q i k (g.comp f) = Phi q j k g * Phi q i j f)
    (S T U : Set A)
    (f : ExactPartialIso P S T)
    (g : ExactPartialIso P T U) :
    P.flattenCoherentRawComponents K Phi S U (g.comp f) =
      P.flattenCoherentRawComponents K Phi T U g *
        P.flattenCoherentRawComponents K Phi S T f := by
  let q : RawIsoComponent P := Quotient.mk P.rawIsoSetoid S
  have hT : Quotient.mk P.rawIsoSetoid T = q :=
    P.exactRawArrow_component_eq S T f
  have hU : Quotient.mk P.rawIsoSetoid U = q :=
    P.exactRawArrow_component_eq S U (g.comp f)
  rw [P.flattenCoherentRawComponents_at K Phi
        S U (g.comp f) q rfl hU,
      P.flattenCoherentRawComponents_at K Phi
        T U g q hT hU,
      P.flattenCoherentRawComponents_at K Phi
        S T f q rfl hT]
  exact hComp q ⟨S, rfl⟩ ⟨T, hT⟩ ⟨U, hU⟩ f g

/-- The global exact groupoid assignment extends the original
literal old vertex map for every exact partial isomorphism. -/
theorem flattenCoherentRawComponents_old
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (psi : A → W)
    (Phi : (q : RawIsoComponent P) →
      (i j : RawComponentObject P q) →
        ExactPartialIso P i.val j.val → K)
    (hOld : ∀ (q : RawIsoComponent P)
      (i j : RawComponentObject P q)
      (f : ExactPartialIso P i.val j.val) (x : i.val),
      (Phi q i j f).val (psi x.val) = psi (f.toEquiv x).val)
    (S T : Set A) (f : ExactPartialIso P S T) (x : S) :
    (P.flattenCoherentRawComponents K Phi S T f).val
      (psi x.val) = psi (f.toEquiv x).val := by
  have hT := P.exactRawArrow_component_eq S T f
  rw [P.flattenCoherentRawComponents_at K Phi
    S T f (Quotient.mk P.rawIsoSetoid S) rfl hT]
  exact hOld (Quotient.mk P.rawIsoSetoid S)
    ⟨S, rfl⟩ ⟨T, hT⟩ f x

end RawRectanglePresentation

end SemigenericEPPA
