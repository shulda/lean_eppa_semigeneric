import SemigenericEPPA.Structure.Pullback

/-!
# Normalizing an arbitrary one-point extension to Option V

The literal one-point SAP theorem uses a standard carrier Option V,
with the old vertices represented by some a and the new vertex by
none. In applications to arbitrary finite diagrams, the old vertices
may instead be embedded by an arbitrary injection f : V → W.

If W consists exactly of f(V) plus one distinguished fresh vertex,
we construct the canonical equivalence Option V ≃ W. Pulling back a
literal R1–R3 structure along this equivalence produces a valid
one-point structure whose old-side E and P_c relations are *exactly*
the original relations restricted along f.

The normalization is also an actual upstream Structure.Embedding.
These facts are the renaming step needed in the iterative SAP proof.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w z

variable {V : Type u} {W : Type v}

/-- A one-point carrier with arbitrary vertex naming is equivalent
to the canonical Option V carrier. The exhaustive-cover assumption
says that *every* vertex is either old or the one genuinely new vertex.
This is an equivalence on real vertices, not on E-classes. -/
noncomputable def onePointCarrierEquiv
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a : V, f a ≠ fresh)
    (hcover : ∀ w : W, w = fresh ∨ ∃ a : V, f a = w) :
    Option V ≃ W := by
  let g : Option V → W
    | none => fresh
    | some a => f a
  have hg : Function.Injective g := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b =>
        have hb : fresh = f b := h
        exact False.elim ((hfresh b) hb.symm)
    | some a =>
      cases y with
      | none =>
        have ha : f a = fresh := h
        exact False.elim ((hfresh a) ha)
      | some b =>
        exact congrArg Option.some (hf h)
  have hs : Function.Surjective g := by
    intro w
    rcases hcover w with hw | ⟨a, ha⟩
    · exact ⟨none, hw.symm⟩
    · exact ⟨some a, ha⟩
  exact Equiv.ofBijective g ⟨hg, hs⟩

@[simp] theorem onePointCarrierEquiv_none
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w) :
    onePointCarrierEquiv f hf fresh hfresh hcover none = fresh := by
  rfl

@[simp] theorem onePointCarrierEquiv_some
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w)
    (a : V) :
    onePointCarrierEquiv f hf fresh hfresh hcover (some a) = f a := by
  rfl

variable {C : Type w}

/-- The literal R1–R3 one-point extension, normalized to the standard
carrier Option V by the equivalence of old and fresh vertices. -/
noncomputable def normalizedOnePoint
    (B : Structure (rectangleLanguage C) W)
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w) :
    Structure (rectangleLanguage C) (Option V) :=
  pullbackRectangle B (onePointCarrierEquiv f hf fresh hfresh hcover)

/-- Old-old E agrees exactly with the original structure pulled back
along the actual old-carrier injection f. -/
theorem normalizedOnePoint_old_part
    (B : Structure (rectangleLanguage C) W)
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w)
    (a b : V) :
    partRel (normalizedOnePoint B f hf fresh hfresh hcover)
        (some a) (some b) ↔
      partRel B (f a) (f b) := by
  simpa [normalizedOnePoint] using
    (pullback_partRel B
      (onePointCarrierEquiv f hf fresh hfresh hcover)
      (some a) (some b))

/-- Every raw colour P_c is likewise preserved and reflected literally,
not merely after applying the effective map φ. -/
theorem normalizedOnePoint_old_raw
    (B : Structure (rectangleLanguage C) W)
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w)
    (c : C) (a b : V) :
    rawRel (normalizedOnePoint B f hf fresh hfresh hcover)
        c (some a) (some b) ↔
      rawRel B c (f a) (f b) := by
  simpa [normalizedOnePoint] using
    (pullback_rawRel B
      (onePointCarrierEquiv f hf fresh hfresh hcover)
      c (some a) (some b))

variable {G : Type z} [Group G] {d : RawDatum G C}

/-- Renaming preserves admissibility of a literal rectangle structure. -/
theorem IsRectangleStructure.normalizedOnePoint
    {B : Structure (rectangleLanguage C) W}
    (h : IsRectangleStructure d B)
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w) :
    IsRectangleStructure d
      (normalizedOnePoint B f hf fresh hfresh hcover) :=
  h.pullback (onePointCarrierEquiv f hf fresh hfresh hcover)

/-- An actual upstream embedding from the normalized one-point
structure into the originally named side, with identity language
component and exactly the prescribed renaming of every vertex. -/
noncomputable def normalizedOnePoint_embedding
    {Γ : Type*} [Group Γ]
    (act : (rectangleLanguage C).Action Γ)
    (B : Structure (rectangleLanguage C) W)
    (f : V → W) (hf : Function.Injective f)
    (fresh : W) (hfresh : ∀ a, f a ≠ fresh)
    (hcover : ∀ w, w = fresh ∨ ∃ a, f a = w) :
    Structure.Embedding act
      (normalizedOnePoint B f hf fresh hfresh hcover) B :=
  pullbackRectangle_embedding act B
    (onePointCarrierEquiv f hf fresh hfresh hcover)
    (onePointCarrierEquiv f hf fresh hfresh hcover).injective

end SemigenericEPPA
