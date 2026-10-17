/-!
# Pasting exact strong-amalgamation squares

A strong amalgam has three *carrier-level* properties:

* The two inclusion maps commute on the common base;
* The images intersect precisely in the common base;
* The two images cover the amalgam carrier.

The cover property, sometimes omitted in existential amalgamation
statements, matters for iterating one-point SAP: it prevents extra
vertices from being silently introduced by an intermediate step.

We formalize these properties without requiring finiteness or a
particular relational language, and prove that strong squares can be
pasted along a shared side. This is the categorical induction lemma
that turns a sequence of verified one-point strong pushouts into a
strong pushout of its endpoints.

No HKN/EPPA existence theorem is used.
-/

namespace SemigenericEPPA

universe u v w x y z

/-- An exact strong-amalgamation square on vertex carriers.
The injections that occur in applications will be supplied by
genuine typed structure embeddings. -/
structure StrongSquare
    {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    (toB : A → B) (toC : A → C)
    (fromB : B → D) (fromC : C → D) : Prop where
  commute : ∀ a, fromB (toB a) = fromC (toC a)
  exact_overlap : ∀ b c,
    fromB b = fromC c ↔ ∃ a, b = toB a ∧ c = toC a
  jointly_surjective :
    ∀ d, (∃ b, fromB b = d) ∨ (∃ c, fromC c = d)

namespace StrongSquare

variable {A : Type u} {B : Type v} {C : Type w}
variable {D : Type x} {E : Type y} {F : Type z}

/-- Interchanging the two sides of a strong square preserves
commutativity, exact overlap and the covering property. -/
theorem swap
    {toB : A → B} {toC : A → C}
    {fromB : B → D} {fromC : C → D}
    (h : StrongSquare toB toC fromB fromC) :
    StrongSquare toC toB fromC fromB := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (h.commute a).symm
  · intro c b
    constructor
    · intro heq
      obtain ⟨a, hb, hc⟩ := (h.exact_overlap b c).mp heq.symm
      exact ⟨a, hc, hb⟩
    · rintro ⟨a, hc, hb⟩
      exact ((h.exact_overlap b c).mpr ⟨a, hb, hc⟩).symm
  · intro d
    rcases h.jointly_surjective d with ⟨b, hb⟩ | ⟨c, hc⟩
    · exact Or.inr ⟨b, hb⟩
    · exact Or.inl ⟨c, hc⟩

/-- Pasting strong squares along the C side. If B and C amalgamate
over A into D, while D and E amalgamate over C into F, then B and E
amalgamate strongly over A into F. In particular the *new* pair of
images covers F; the intermediate amalgamation adds no phantom
vertices. -/
theorem paste
    {toB : A → B} {toC : A → C}
    {fromB : B → D} {fromC : C → D}
    {toE : C → E} {fromD : D → F} {fromE : E → F}
    (h₁ : StrongSquare toB toC fromB fromC)
    (h₂ : StrongSquare fromC toE fromD fromE) :
    StrongSquare toB (toE ∘ toC) (fromD ∘ fromB) fromE := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    calc
      (fromD ∘ fromB) (toB a) =
          fromD (fromC (toC a)) :=
        congrArg fromD (h₁.commute a)
      _ = fromE (toE (toC a)) := h₂.commute (toC a)
  · intro b e
    constructor
    · intro heq
      have heq' : fromD (fromB b) = fromE e := heq
      obtain ⟨c, hbc, hec⟩ :=
        (h₂.exact_overlap (fromB b) e).mp heq'
      obtain ⟨a, hb, hc⟩ := (h₁.exact_overlap b c).mp hbc
      refine ⟨a, hb, ?_⟩
      exact hec.trans (congrArg toE hc)
    · rintro ⟨a, hb, he⟩
      change fromD (fromB b) = fromE e
      calc
        fromD (fromB b) = fromD (fromB (toB a)) := by rw [hb]
        _ = fromD (fromC (toC a)) :=
          congrArg fromD (h₁.commute a)
        _ = fromE (toE (toC a)) := h₂.commute (toC a)
        _ = fromE e := by rw [he]
  · intro f
    rcases h₂.jointly_surjective f with ⟨d, hd⟩ | ⟨e, he⟩
    · rcases h₁.jointly_surjective d with ⟨b, hb⟩ | ⟨c, hc⟩
      · left
        refine ⟨b, ?_⟩
        exact (congrArg fromD hb).trans hd
      · right
        refine ⟨toE c, ?_⟩
        calc
          fromE (toE c) = fromD (fromC c) := (h₂.commute c).symm
          _ = fromD d := congrArg fromD hc
          _ = f := hd
    · exact Or.inr ⟨e, he⟩

/-- The identity span on the left is already a strong square.
This is a base case for successive amalgamation. -/
theorem identity_left
    {A : Type u} {C : Type w} (toC : A → C) :
    StrongSquare (id : A → A) toC toC (id : C → C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a c
    constructor
    · intro h
      exact ⟨a, rfl, h.symm⟩
    · rintro ⟨x, ha, hc⟩
      change toC a = c
      calc
        toC a = toC x := by rw [ha]
        _ = c := hc.symm
  · intro c
    exact Or.inr ⟨c, rfl⟩

/-- The symmetric identity base case. -/
theorem identity_right
    {A : Type u} {B : Type v} (toB : A → B) :
    StrongSquare toB (id : A → A) (id : B → B) toB := by
  exact (identity_left toB).swap

end StrongSquare
end SemigenericEPPA
