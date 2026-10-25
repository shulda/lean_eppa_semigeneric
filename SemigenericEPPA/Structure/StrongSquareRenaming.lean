import SemigenericEPPA.Structure.StrongSquare

/-!
# Reindexing strong-amalgamation squares by actual carrier equivalences

The finite-SAP normalizations enumerate the complementary vertices
of each old-side embedding, giving actual equivalences between
an arbitrary finite carrier and a canonical old-plus-Fin carrier.

Here we verify once and for all that changing the names of the
two sides, or the amalgam target, transports the *exact* square:
- commutativity on the old base;
- intersection precisely in the old base;
- joint surjectivity (no invisible extra vertices).

This is pure carrier-level reasoning and does not assume any
mathematical property of the underlying relations.
-/

namespace SemigenericEPPA

universe u v w x y z

namespace StrongSquare

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
variable {B' : Type y} {C' : Type z}

/-- Transport BOTH side carriers of a strong square across
arbitrary bijections, without changing the common old base. -/
theorem reindexSides
    {toB : A → B} {toC : A → C}
    {fromB : B → D} {fromC : C → D}
    (h : StrongSquare toB toC fromB fromC)
    (eB : B' ≃ B) (eC : C' ≃ C) :
    StrongSquare
      (eB.symm ∘ toB) (eC.symm ∘ toC)
      (fromB ∘ eB) (fromC ∘ eC) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    change fromB (eB (eB.symm (toB a))) =
      fromC (eC (eC.symm (toC a)))
    simpa only [Equiv.apply_symm_apply] using h.commute a
  · intro b c
    change fromB (eB b) = fromC (eC c) ↔
      ∃ a, b = eB.symm (toB a) ∧ c = eC.symm (toC a)
    constructor
    · intro heq
      obtain ⟨a, hb, hc⟩ := (h.exact_overlap (eB b) (eC c)).mp heq
      refine ⟨a, ?_, ?_⟩
      · apply eB.injective
        simpa only [Equiv.apply_symm_apply] using hb
      · apply eC.injective
        simpa only [Equiv.apply_symm_apply] using hc
    · rintro ⟨a, hb, hc⟩
      apply (h.exact_overlap (eB b) (eC c)).mpr
      refine ⟨a, ?_, ?_⟩
      · rw [hb, Equiv.apply_symm_apply]
      · rw [hc, Equiv.apply_symm_apply]
  · intro d
    rcases h.jointly_surjective d with ⟨b, hb⟩ | ⟨c, hc⟩
    · left
      refine ⟨eB.symm b, ?_⟩
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hb
    · right
      refine ⟨eC.symm c, ?_⟩
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc

/-- Reindex the common OLD BASE by a bijection. Exact overlap
is preserved because the new base still enumerates every old
point exactly once. -/
theorem reindexBase
    {toB : A → B} {toC : A → C}
    {fromB : B → D} {fromC : C → D}
    {A' : Type y}
    (h : StrongSquare toB toC fromB fromC)
    (eA : A' ≃ A) :
    StrongSquare (toB ∘ eA) (toC ∘ eA) fromB fromC := by
  refine ⟨?_, ?_, h.jointly_surjective⟩
  · intro a
    exact h.commute (eA a)
  · intro b c
    constructor
    · intro heq
      obtain ⟨a, hb, hc⟩ := (h.exact_overlap b c).mp heq
      refine ⟨eA.symm a, ?_, ?_⟩
      · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hb
      · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc
    · rintro ⟨a, hb, hc⟩
      exact (h.exact_overlap b c).mpr ⟨eA a, hb, hc⟩

/-- Transport the target carrier of a strong square by a
bijection; exact overlap is preserved by injectivity. -/
theorem reindexTarget
    {toB : A → B} {toC : A → C}
    {fromB : B → D} {fromC : C → D}
    {D' : Type y}
    (h : StrongSquare toB toC fromB fromC)
    (eD : D ≃ D') :
    StrongSquare toB toC (eD ∘ fromB) (eD ∘ fromC) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact congrArg eD (h.commute a)
  · intro b c
    change eD (fromB b) = eD (fromC c) ↔
      ∃ a, b = toB a ∧ c = toC a
    constructor
    · intro heq
      exact (h.exact_overlap b c).mp (eD.injective heq)
    · intro heq
      exact congrArg eD ((h.exact_overlap b c).mpr heq)
  · intro d
    rcases h.jointly_surjective (eD.symm d) with ⟨b, hb⟩ | ⟨c, hc⟩
    · exact Or.inl ⟨b, by
        change eD (fromB b) = d
        rw [hb, Equiv.apply_symm_apply]⟩
    · exact Or.inr ⟨c, by
        change eD (fromC c) = d
        rw [hc, Equiv.apply_symm_apply]⟩

end StrongSquare
end SemigenericEPPA
