import SemigenericEPPA.Bridge.FlattenCoherentRawGroupoid

/-!
# Generic coherent raw groupoid from one automorphism group and connectors

A coherent extension functor requires a homomorphic lift of each
induced old automorphism group and arbitrary individual extensions
for old connectors, all inside the SAME fixed whole-witness raw
automorphism subgroup, using the SAME fixed old embedding.

These two APIs are sufficient. The previously formalized
representative-based component construction chooses one reference
and one connector for each isomorphism component of the exact
old partial-isomorphism groupoid. Flattening the components
yields a single global functor satisfying strict identity,
composition and literal old-vertex extension.

The argument is entirely generic: no finiteness, effective group,
saturation, self-reversing colour or valuation construction is
needed here. The positive nontrivial-G construction supplies
these hypotheses via the one-fixed-witness group/connector theorem.
-/

namespace SemigenericEPPA

universe u v w t
variable {G : Type u} [Group G]
variable {C : Type v} {A : Type w} {W : Type t}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- If one original P and one fixed whole-witness group K support
all stabilizer homomorphisms and all raw connector extensions,
then they support a SINGLE strictly coherent assignment of ALL
exact old raw groupoid arrows, extending them on the same old map. -/
theorem exists_globalCoherentExactRawFunctor_of_groupsAndConnectors
    (P : RawRectanglePresentation d A)
    (K : Subgroup (Equiv.Perm W))
    (psi : A → W)
    (hGroups : ∀ (S : Set A),
      ∃ rho : ExactPartialIso P S S →* K,
        ∀ (h : ExactPartialIso P S S) (x : S),
          (rho h).val (psi x.val) = psi (h.toEquiv x).val)
    (hConnector : ∀ (S T : Set A)
        (f : ExactPartialIso P S T),
      ∃ beta : K,
        ∀ x : S,
          beta.val (psi x.val) = psi (f.toEquiv x).val) :
    ∃ F : (S T : Set A) → ExactPartialIso P S T → K,
      (∀ (S : Set A),
        F S S (ExactPartialIso.refl P S) = 1) ∧
      (∀ (S T U : Set A)
        (f : ExactPartialIso P S T)
        (g : ExactPartialIso P T U),
        F S U (g.comp f) = F T U g * F S T f) ∧
      (∀ (S T : Set A) (f : ExactPartialIso P S T) (x : S),
        (F S T f).val (psi x.val) =
          psi (f.toEquiv x).val) := by
  classical
  obtain ⟨Phi, hId, hComp, hOld⟩ :=
    P.exists_coherentRawLifts_onEveryComponent K psi
      hGroups hConnector
  let F : (S T : Set A) → ExactPartialIso P S T → K :=
    fun S T f => P.flattenCoherentRawComponents K Phi S T f
  refine ⟨F, ?_, ?_, ?_⟩
  · intro S
    exact P.flattenCoherentRawComponents_id K Phi hId S
  · intro S T U f g
    exact P.flattenCoherentRawComponents_comp
      K Phi hComp S T U f g
  · intro S T f x
    exact P.flattenCoherentRawComponents_old
      K psi Phi hOld S T f x

end RawRectanglePresentation

end SemigenericEPPA
