import SemigenericEPPA.Structure.DLFSafePairTowerAgeSchedule
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.Fin

/-!
# A countable canonical schedule of every finite original raw rectangle

The original language has a finite raw alphabet C. On each finite
carrier Fin n, a RawRectanglePresentation is determined by its two
data functions: the E relation Fin n → Fin n → Prop and the ordered
Option C raw colour function. Their remaining fields are PROOFS,
so by proof irrelevance every such finite-carrier presentation type
is itself finite.

Consequently the disjoint sum Σ n, RawRectanglePresentation d (Fin n)
is countable. It is nonempty (the empty carrier carries the unique
empty raw rectangle), and so there is a surjection ℕ onto this
disjoint sum. This yields a canonical noncomputable schedule of
finite raw rectangles, covering literally every Fin n presentation.

The theorem supplies the final enumeration ingredient for the
age-cofinal DLF safe-pair tower. No chosen structure is required to
satisfy coherence or any good-colour condition.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- A genuine empty original R1–R3 raw rectangle on Fin 0,
available without assumptions on good colours. -/
noncomputable def emptyFiniteRaw :
    RawRectanglePresentation d (Fin 0) where
  part := fun x _ => Fin.elim0 x
  part_equiv := by
    constructor
    · intro x
      exact Fin.elim0 x
    · intro x
      exact Fin.elim0 x
    · intro x
      exact Fin.elim0 x
  colour := fun x _ => Fin.elim0 x
  colour_none_iff := by
    intro x
    exact Fin.elim0 x
  colour_reverse := by
    intro x
    exact Fin.elim0 x
  rectangle := by
    intro x
    exact Fin.elim0 x

/-- There are only finitely many literal raw R1–R3 structures on
Fin n. No quotient by isomorphisms is required. -/
private theorem finiteRawPresentation_onFin (n : ℕ) :
    Finite (RawRectanglePresentation d (Fin n)) := by
  classical
  have hInj : Function.Injective
      (fun P : RawRectanglePresentation d (Fin n) =>
        (P.part, P.colour)) := by
    intro P Q h
    rcases P with ⟨part, pe, colour, none, reverse, rect⟩
    rcases Q with ⟨part', pe', colour', none', reverse', rect'⟩
    have hp : part = part' := congrArg Prod.fst h
    have hc : colour = colour' := congrArg Prod.snd h
    subst part'
    subst colour'
    rfl
  exact Finite.of_injective _ hInj

/-- There is a literal surjective enumeration of ALL finite raw
rectangles carried on canonical finite sets Fin n. -/
theorem exists_surjective_canonicalFiniteRawSchedule :
    ∃ e : ℕ → (Σ n : ℕ, RawRectanglePresentation d (Fin n)),
      Function.Surjective e := by
  classical
  letI : ∀ n : ℕ, Finite (RawRectanglePresentation d (Fin n)) :=
    fun n => finiteRawPresentation_onFin n
  have hCount :
      Countable (Σ n : ℕ, RawRectanglePresentation d (Fin n)) :=
    inferInstance
  letI : Nonempty (Σ n : ℕ, RawRectanglePresentation d (Fin n)) :=
    ⟨⟨0, emptyFiniteRaw (d := d)⟩⟩
  exact countable_iff_exists_surjective.mp hCount

/-- The chosen surjective schedule of all original finite
R1–R3 presentations on Fin n, in the canonical common universe. -/
noncomputable def canonicalFiniteRawSchedule :
    ℕ → (Σ n : ℕ, RawRectanglePresentation d (Fin n)) :=
  Classical.choose (exists_surjective_canonicalFiniteRawSchedule (d := d))

theorem canonicalFiniteRawSchedule_surjective :
    Function.Surjective (canonicalFiniteRawSchedule (d := d)) :=
  Classical.choose_spec (exists_surjective_canonicalFiniteRawSchedule (d := d))

/-- The actual fixed-universe packaged targets for the age-cofinal
safe-pair tower: every canonical finite raw rectangle appears
at some natural stage in this sequence. -/
noncomputable def canonicalFiniteRawTargets :
    ℕ → FiniteRawAgeTarget d :=
  fun i =>
    let a := canonicalFiniteRawSchedule (d := d) i
    {
      carrier := Fin a.1
      finite_carrier := inferInstance
      raw := a.2
    }

end SemigenericEPPA
