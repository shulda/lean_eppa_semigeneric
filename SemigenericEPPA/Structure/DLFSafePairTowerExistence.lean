import SemigenericEPPA.Structure.DLFFiniteSafePairOneStep
import SemigenericEPPA.Structure.DLFSafePairTowerConditionalDensity

/-!
# Existence of a genuine infinite finite-safe-pair tower with all connectors

For one complete good affine congruence orbit, the certified
finite successor theorem extends ANY finite actual safe
(A,H≤Aut_raw(A)) to a finite safe (B,K), with strict equivariant
injective H→K and one common K realizing every original partial
raw automorphism of A.

Package varying finite carrier types in ONE fixed universe
(max u v) and iterate this existence theorem by classical
choice. The output is a concrete ℕ-indexed genuine finite
safe-pair tower, together with the exact next-stage connector
property required by the quotient-limit homogeneity and density
theorems.

No finite AGE-COFINALITY is asserted; this tower need not yet
contain all prescribed finite original raw rectangles.
The separate JEP/age-target successor program will add that
requirement to the same recursion.
-/

namespace SemigenericEPPA

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {C : Type v} [Finite C]
variable {d : RawDatum G C}

/-- An actual finite safe original raw pair packaged with its
finite carrier, in the fixed universe of the group/colour data. -/
structure FiniteSafePairState (d : RawDatum G C) where
  carrier : Type (max u v)
  finite_carrier : Finite carrier
  pair : letI : Finite carrier := finite_carrier
         FiniteSafeRawPair d carrier

namespace FiniteSafePairState

/-- Strict finite-safe-pair successor together with actual
next-stage connectors for EVERY old partial raw automorphism. -/
def HasConnectorSuccessor
    (A B : FiniteSafePairState d) : Prop :=
  letI : Finite A.carrier := A.finite_carrier
  letI : Finite B.carrier := B.finite_carrier
  ∃ f : FiniteSafeRawPairEmbedding A.pair B.pair,
    ∀ (S : Set A.carrier) (p : S → A.carrier),
      Function.Injective p →
      (∀ x y : S, A.pair.raw.part x.val y.val ↔
        A.pair.raw.part (p x) (p y)) →
      (∀ x y : S, A.pair.raw.colour (p x) (p y) =
        A.pair.raw.colour x.val y.val) →
      ∃ k : B.pair.subgroup, ∀ x : S,
        k.val.val (f.vertex x.val) = f.vertex (p x)

/-- A single complete good affine orbit supplies one genuine
successor in the SAME fixed carrier universe with all connectors. -/
theorem exists_connectorSuccessor
    (A : FiniteSafePairState d)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ B : FiniteSafePairState d, A.HasConnectorSuccessor B := by
  classical
  letI : Finite A.carrier := A.finite_carrier
  letI : Fintype A.carrier := Fintype.ofFinite A.carrier
  obtain ⟨W, hW, B, f, hPartials⟩ :=
    A.pair.exists_safeExtension_withAllPartialMaps hOrbit
  letI : Finite W := hW
  let next : FiniteSafePairState d := {
    carrier := W
    finite_carrier := hW
    pair := B
  }
  exact ⟨next, f, hPartials⟩

/-- Chosen safe successor. Existence is certified by the exact
original-language finite relative safe EPPA construction. -/
private noncomputable def next
    (hOrbit : d.HasCompleteGoodOrbit)
    (A : FiniteSafePairState d) : FiniteSafePairState d :=
  Classical.choose (A.exists_connectorSuccessor hOrbit)

private theorem next_spec
    (hOrbit : d.HasCompleteGoodOrbit)
    (A : FiniteSafePairState d) :
    A.HasConnectorSuccessor (next hOrbit A) :=
  Classical.choose_spec (A.exists_connectorSuccessor hOrbit)

/-- Infinite sequence of finite safe pair states, defined by actual
successive classical choices of the certified finite witness. -/
private noncomputable def seq
    (hOrbit : d.HasCompleteGoodOrbit)
    (A₀ : FiniteSafePairState d) :
    ℕ → FiniteSafePairState d
  | 0 => A₀
  | n + 1 => next hOrbit (seq hOrbit A₀ n)

/-- The chosen successor is strict and extends all old partial
raw maps by elements of the NEXT finite subgroup. -/
private theorem seq_step
    (hOrbit : d.HasCompleteGoodOrbit)
    (A₀ : FiniteSafePairState d) (n : ℕ) :
    HasConnectorSuccessor
      (seq hOrbit A₀ n) (seq hOrbit A₀ (n + 1)) :=
  next_spec hOrbit (seq hOrbit A₀ n)

end FiniteSafePairState

/-- Under ONE complete good orbit, every finite safe pair is the
first stage of a genuine countable chain of finite safe raw pairs
with strict equivariant subgroup maps and ALL next-stage partial
raw connectors. This is a full tower existence theorem, but the
AGE-COFINALITY requirement is not yet imposed. -/
theorem exists_safeTower_with_nextStageConnectors
    (A₀ : FiniteSafePairState d)
    (hOrbit : d.HasCompleteGoodOrbit) :
    ∃ (V : ℕ → Type (max u v))
      (hV : ∀ n, Finite (V n)),
      letI : ∀ n, Finite (V n) := hV
      ∃ T : FiniteSafeRawPairTower d V,
        T.HasNextStageRawConnectors ∧ V 0 = A₀.carrier := by
  classical
  let states : ℕ → FiniteSafePairState d :=
    FiniteSafePairState.seq hOrbit A₀
  have hSucc (n : ℕ) :
      FiniteSafePairState.HasConnectorSuccessor
        (states n) (states (n+1)) :=
    FiniteSafePairState.seq_step hOrbit A₀ n
  let V : ℕ → Type (max u v) := fun n => (states n).carrier
  let hV : ∀ n, Finite (V n) := fun n => (states n).finite_carrier
  letI : ∀ n, Finite (V n) := hV
  let T : FiniteSafeRawPairTower d V := {
    stage := fun n => (states n).pair
    step := fun n => Classical.choose (hSucc n)
  }
  refine ⟨V, hV, T, ?_, ?_⟩
  · intro n S p hp hPart hColour
    exact (Classical.choose_spec (hSucc n)) S p hp hPart hColour
  · rfl

end SemigenericEPPA
