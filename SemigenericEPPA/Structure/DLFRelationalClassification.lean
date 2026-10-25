import SemigenericEPPA.Structure.DLFRelationalAutomorphismBridge
import SemigenericEPPA.Structure.DLFCompleteClassification

/-!
# A named DLF iff entirely in the original AllThoseEPPA relational language

The exact raw DLF classification already constructs a literal
original-language rectangle, but its public predicate quantifies
over functional raw presentations. The paper states its theorem
for the Fraisse class in the original binary symbols E and R_c.

Here the class predicate and automorphism subgroup are expressed
directly using AllThoseEPPA.Structure (rectangleLanguage C),
IsRectangleStructure, partRel, and ALL rawRel predicates.
The real relational full automorphism group is identified exactly
with the raw full group by DLFRelationalAutomorphismBridge, not
replaced by an abstract group.

Raw colour equality is logically equivalent to simultaneous
preservation of EVERY rawRel predicate; this conversion and the
two directions of the DLF criterion are proved explicitly.
The age quantifies all finite canonical raw presentations, each
of which is exactly an original relational R1–R3 member, and all
arbitrary finite original relational carriers reduce to Fin n
by the already-certified exact raw/relational bridge.

No extra algebraic conditions, Sagi correspondence, HKN theorem,
or independent Fraisse existence axiom enter this formulation.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

namespace IsRectangleStructure

variable {V : Type w}
variable {A : Structure (rectangleLanguage C) V}

/-- Literal preservation of every ordered R_c predicate implies
equality of the canonical Option-C raw colours. -/
theorem rawOption_eq_of_allRelEquiv
    (h : IsRectangleStructure d A)
    (x y z w : V)
    (hRel : ∀ c : C,
      rawRel A c x y ↔ rawRel A c z w) :
    h.toRawPresentation.colour x y =
      h.toRawPresentation.colour z w := by
  change h.rawOption x y = h.rawOption z w
  cases hx : h.rawOption x y with
  | none =>
      cases hz : h.rawOption z w with
      | none =>
          rfl
      | some c =>
          have hRelZ : rawRel A c z w :=
            (h.rawOption_some_iff c z w).mp hz
          have hRelX : rawRel A c x y := (hRel c).mpr hRelZ
          have hRawX : h.rawOption x y = some c :=
            (h.rawOption_some_iff c x y).mpr hRelX
          rw [hx] at hRawX
          cases hRawX
  | some c =>
      have hRelX : rawRel A c x y :=
        (h.rawOption_some_iff c x y).mp hx
      have hRelZ : rawRel A c z w := (hRel c).mp hRelX
      have hRawZ : h.rawOption z w = some c :=
        (h.rawOption_some_iff c z w).mpr hRelZ
      exact hRawZ.symm

/-- Equality of canonical raw options preserves and reflects
every ordered original relation symbol R_c. -/
theorem rawRel_iff_of_rawOption_eq
    (h : IsRectangleStructure d A)
    (x y z w : V)
    (heq : h.toRawPresentation.colour x y =
      h.toRawPresentation.colour z w)
    (c : C) :
    rawRel A c x y ↔ rawRel A c z w := by
  have hColour : h.rawOption x y = h.rawOption z w := heq
  calc
    rawRel A c x y ↔ h.rawOption x y = some c :=
      (h.rawOption_some_iff c x y).symm
    _ ↔ h.rawOption z w = some c := by rw [hColour]
    _ ↔ rawRel A c z w := h.rawOption_some_iff c z w

end IsRectangleStructure

namespace RawDatum

/-- Countable homogeneous full-age DLF expressed using the
ACTUAL original relational R1–R3 structure A, exact E and R_c
predicates, and the actual relational automorphism subgroup. -/
def HasCountableRelationalHomogeneousDLF
    (d : RawDatum G C) : Prop :=
  ∃ (X : Type (max u v))
    (A : Structure (rectangleLanguage C) X)
    (hA : IsRectangleStructure d A),
    Countable X ∧
    (∀ (n : ℕ) (P : RawRectanglePresentation d (Fin n)),
      ∃ e : Fin n → X,
        Function.Injective e ∧
        (∀ x y : Fin n,
          partRel A (e x) (e y) ↔ P.part x y) ∧
        (∀ (c : C) (x y : Fin n),
          rawRel A c (e x) (e y) ↔ P.colour x y = some c)) ∧
    (∀ (F : Finset X) (p : F → X),
      Function.Injective p →
      (∀ x y : F,
        partRel A (p x) (p y) ↔ partRel A x.val y.val) →
      (∀ (c : C) (x y : F),
        rawRel A c (p x) (p y) ↔ rawRel A c x.val y.val) →
      ∃ a : relationalFullAutGroup A,
        ∀ x : F, a.val x.val = p x) ∧
    (∃ L : Subgroup (Equiv.Perm X),
      L ≤ relationalFullAutGroup A ∧
      DenseByFiniteRestrictions (relationalFullAutGroup A) L ∧
      EveryFinitelyGeneratedSubgroupFinite L)

/-- The relational DLF predicate is EXACTLY the functional raw
predicate, on the SAME vertex carrier and SAME automorphism
subgroup. Neither direction takes an abstract group quotient. -/
theorem countableRelationalHomogeneousDLF_iff_raw
    (d : RawDatum G C) :
    d.HasCountableRelationalHomogeneousDLF ↔
      d.HasCountableHomogeneousDLF := by
  classical
  constructor
  · rintro ⟨X, A, hA, hCount, hAge, hHom, hDLF⟩
    refine ⟨X, hA.toRawPresentation, hCount, ?_, ?_, ?_⟩
    · intro n P
      obtain ⟨e, he, hPart, hRaw⟩ := hAge n P
      refine ⟨e, he, hPart, ?_⟩
      intro x y
      cases hc : P.colour x y with
      | none =>
          have hPPart : P.part x y := (P.colour_none_iff x y).mp hc
          have hAPart : partRel A (e x) (e y) :=
            (hPart x y).mpr hPPart
          exact (hA.rawOption_none_iff (e x) (e y)).mpr hAPart
      | some c =>
          have hcRel : rawRel A c (e x) (e y) :=
            (hRaw c x y).mpr hc
          exact (hA.rawOption_some_iff c (e x) (e y)).mpr hcRel
    · intro F p hp hPart hColour
      have hRel : ∀ (c : C) (x y : F),
          rawRel A c (p x) (p y) ↔ rawRel A c x.val y.val := by
        intro c x y
        exact hA.rawRel_iff_of_rawOption_eq
          (p x) (p y) x.val y.val (hColour x y) c
      rw [← hA.relationalFullAutGroup_eq_raw]
      exact hHom F p hp hPart hRel
    · simpa only [hA.relationalFullAutGroup_eq_raw] using hDLF
  · rintro ⟨X, M, hCount, hAge, hHom, hDLF⟩
    let A : Structure (rectangleLanguage C) X := M.toStructure
    let hA : IsRectangleStructure d A := M.toStructure_isRectangleStructure
    refine ⟨X, A, hA, hCount, ?_, ?_, ?_⟩
    · intro n P
      obtain ⟨e, he, hPart, hColour⟩ := hAge n P
      refine ⟨e, he, hPart, ?_⟩
      intro c x y
      change M.colour (e x) (e y) = some c ↔
        P.colour x y = some c
      rw [hColour x y]
    · intro F p hp hPart hRaw
      have hOption : ∀ x y : F,
          M.colour (p x) (p y) = M.colour x.val y.val := by
        intro x y
        have hh :=
          hA.rawOption_eq_of_allRelEquiv
            (p x) (p y) x.val y.val
            (fun c => hRaw c x y)
        change hA.rawOption (p x) (p y) =
          hA.rawOption x.val y.val at hh
        simpa only [M.toStructure_rawOption_eq] using hh
      rw [← M.fullRawAutGroup_eq_relational]
      exact hHom F p hp hPart hOption
    · simpa only [M.fullRawAutGroup_eq_relational] using hDLF

/-- Fully original-relational version of the complete DLF iff:
G is trivial OR one whole good affine congruence orbit exists.
Every group/subgroup in the DLF predicate is a true automorphism
of the original AllThoseEPPA.Structure (rectangleLanguage C). -/
theorem countableRelationalHomogeneousDLF_iff
    (d : RawDatum G C) :
    d.HasCountableRelationalHomogeneousDLF ↔
      Subsingleton G ∨ d.HasCompleteGoodOrbit :=
  (d.countableRelationalHomogeneousDLF_iff_raw).trans
    (d.countableHomogeneousDLF_iff)

end RawDatum
end SemigenericEPPA
