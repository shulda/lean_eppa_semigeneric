import SemigenericEPPA.Structure.OnePointNormalization
import SemigenericEPPA.Structure.Induced
import Mathlib.Data.Set.Insert

/-!
# Adding one vertex to an arbitrary induced substructure

The one-point SAP theorem is phrased on \`Option V\`. When inducting over
finite diagrams, its input is an arbitrary old vertex subset S of a
larger carrier and a new vertex x outside S.

Here we give an exact vertex equivalence
  Option S ≃ {v // v ∈ insert x S}
and pull back the ambient induced structure. Every old E and P_c
relation is preserved exactly, and the resulting map back to the
one-point extension is a genuine AllThoseEPPA.Structure.Embedding.

No finiteness, order, group commutativity or EPPA hypothesis occurs
in this reindexing result.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {V : Type u}

/-- Old vertices of S, viewed as vertices of the extension S ∪ {x}. -/
def adjoinOld (S : Set V) (x : V) :
    S → {v : V // v ∈ insert x S} :=
  fun a => ⟨a.val, Set.mem_insert_of_mem x a.property⟩

/-- The genuinely fresh vertex of S ∪ {x}. -/
def adjoinFresh (S : Set V) (x : V) :
    {v : V // v ∈ insert x S} :=
  ⟨x, Set.mem_insert x S⟩

theorem adjoinOld_injective (S : Set V) (x : V) :
    Function.Injective (adjoinOld S x) := by
  intro a b h
  apply Subtype.ext
  exact congrArg
    (fun v : {v : V // v ∈ insert x S} => (v : V)) h

/-- Freshness as an inequality of actual vertices, not E-classes. -/
theorem adjoinFresh_not_old (S : Set V) (x : V) (hx : x ∉ S)
    (a : S) : adjoinOld S x a ≠ adjoinFresh S x := by
  intro h
  have hax : a.val = x := congrArg Subtype.val h
  exact hx (hax ▸ a.property)

/-- Every vertex of S ∪ {x} is either the fresh one or an old vertex. -/
theorem adjoinOld_cover (S : Set V) (x : V)
    (a : {v : V // v ∈ insert x S}) :
    a = adjoinFresh S x ∨ ∃ b : S, adjoinOld S x b = a := by
  rcases (Set.mem_insert_iff).mp a.property with ha | ha
  · left
    exact Subtype.ext ha
  · right
    refine ⟨⟨a.val, ha⟩, ?_⟩
    rfl

/-- The canonical one-point encoding of an arbitrary vertex addition.
The ambient carrier need not be finite. -/
noncomputable def adjoinEquiv (S : Set V) (x : V) (hx : x ∉ S) :
    Option S ≃ {v : V // v ∈ insert x S} :=
  onePointCarrierEquiv (adjoinOld S x)
    (adjoinOld_injective S x)
    (adjoinFresh S x)
    (adjoinFresh_not_old S x hx)
    (adjoinOld_cover S x)

@[simp] theorem adjoinEquiv_none (S : Set V) (x : V) (hx : x ∉ S) :
    adjoinEquiv S x hx none = adjoinFresh S x := by
  exact onePointCarrierEquiv_none (adjoinOld S x)
    (adjoinOld_injective S x) (adjoinFresh S x)
    (adjoinFresh_not_old S x hx) (adjoinOld_cover S x)

@[simp] theorem adjoinEquiv_some (S : Set V) (x : V) (hx : x ∉ S)
    (a : S) :
    adjoinEquiv S x hx (some a) = adjoinOld S x a := by
  exact onePointCarrierEquiv_some (adjoinOld S x)
    (adjoinOld_injective S x) (adjoinFresh S x)
    (adjoinFresh_not_old S x hx) (adjoinOld_cover S x) a

variable {C : Type v}

/-- Induced structure after adding a single outside vertex, encoded
on \`Option S\` so it is ready for literal one-point SAP. -/
noncomputable def adjoinInduced
    (A : Structure (rectangleLanguage C) V)
    (S : Set V) (x : V) (hx : x ∉ S) :
    Structure (rectangleLanguage C) (Option S) :=
  pullbackRectangle (inducedRectangle A (insert x S))
    (adjoinEquiv S x hx)

/-- The E-relation on old vertices is unchanged by adjoining x. -/
theorem adjoinInduced_old_part
    (A : Structure (rectangleLanguage C) V)
    (S : Set V) (x : V) (hx : x ∉ S) (a b : S) :
    partRel (adjoinInduced A S x hx) (some a) (some b) ↔
      partRel (inducedRectangle A S) a b := by
  rw [adjoinInduced, pullback_partRel,
    adjoinEquiv_some, adjoinEquiv_some]
  exact (inducedRectangle_part A (insert x S)
    (adjoinOld S x a) (adjoinOld S x b)).trans
    (inducedRectangle_part A S a b).symm

/-- All old raw-colour predicates are literally unchanged. -/
theorem adjoinInduced_old_raw
    (A : Structure (rectangleLanguage C) V)
    (S : Set V) (x : V) (hx : x ∉ S)
    (c : C) (a b : S) :
    rawRel (adjoinInduced A S x hx) c (some a) (some b) ↔
      rawRel (inducedRectangle A S) c a b := by
  rw [adjoinInduced, pullback_rawRel,
    adjoinEquiv_some, adjoinEquiv_some]
  exact (inducedRectangle_raw A (insert x S) c
    (adjoinOld S x a) (adjoinOld S x b)).trans
    (inducedRectangle_raw A S c a b).symm

variable {G : Type w} [Group G] {d : RawDatum G C}

/-- Adjoining x does not leave the R1–R3 class. -/
theorem IsRectangleStructure.adjoinInduced
    {A : Structure (rectangleLanguage C) V}
    (h : IsRectangleStructure d A)
    (S : Set V) (x : V) (hx : x ∉ S) :
    IsRectangleStructure d (adjoinInduced A S x hx) :=
  (h.induced (insert x S)).pullback (adjoinEquiv S x hx)

/-- The adjoined structure genuinely embeds in the induced structure
on S ∪ {x}, with identity language component. -/
noncomputable def adjoinInduced_embedding
    {Γ : Type z} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (A : Structure (rectangleLanguage C) V)
    (S : Set V) (x : V) (hx : x ∉ S) :
    Structure.Embedding act (adjoinInduced A S x hx)
      (inducedRectangle A (insert x S)) :=
  pullbackRectangle_embedding act (inducedRectangle A (insert x S))
    (adjoinEquiv S x hx)
    (adjoinEquiv S x hx).injective

end SemigenericEPPA
