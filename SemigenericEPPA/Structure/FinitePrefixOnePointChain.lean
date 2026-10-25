import SemigenericEPPA.Structure.OnePointChainSAP
import SemigenericEPPA.Structure.Pullback
import Mathlib.Tactic

/-!
# Canonical finite one-point chain inside an arbitrary finite extension

For any valid original-language rectangle on X ⊕ Fin m, the
induced prefix structures on X ⊕ Fin (min n m) form a genuine
finite one-point chain of length m. At successor n < m there
is exactly one new vertex: the index n. The inclusion
embeddings are induced for E AND every ordered R_c.

This is a concrete finite-exhaustion lemma required to pass
from one-point amalgamation to arbitrary finite strong SAP.
No order on X, raw palette, or effective group is added.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- The prefix with the first min(n,m) new vertices of an
original finite extension having m distinguished new vertices. -/
abbrev PrefixCarrier (X : Type w) (m n : ℕ) :=
  X ⊕ Fin (min n m)

/-- The canonical embedding of any prefix into the final
original vertex carrier. -/
def prefixToFinal {X : Type w} (m n : ℕ) :
    PrefixCarrier X m n → X ⊕ Fin m
  | Sum.inl a => Sum.inl a
  | Sum.inr i => Sum.inr ⟨i.val, by have hi := i.isLt; omega⟩

/-- The literal inclusion of the n-prefix into the (n+1)-prefix. -/
def prefixStep {X : Type w} (m n : ℕ) (hn : n < m) :
    PrefixCarrier X m n → PrefixCarrier X m (n+1)
  | Sum.inl a => Sum.inl a
  | Sum.inr i => Sum.inr ⟨i.val, by have hi := i.isLt; omega⟩

theorem prefixStep_injective {X : Type w} (m n : ℕ) (hn : n < m) :
    Function.Injective (prefixStep (X := X) m n hn) := by
  intro x y h
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          have hab : a = b := Sum.inl.inj (by simpa [prefixStep] using h)
          exact congrArg Sum.inl hab
      | inr b =>
          simp [prefixStep] at h
  | inr a =>
      cases y with
      | inl b =>
          simp [prefixStep] at h
      | inr b =>
          have hab : a.val = b.val := by
            have heq : (⟨a.val, by have hi := a.isLt; omega⟩ :
                Fin (min (n+1) m)) =
                ⟨b.val, by have hi := b.isLt; omega⟩ :=
              Sum.inr.inj (by simpa [prefixStep] using h)
            exact congrArg Fin.val heq
          exact congrArg Sum.inr (Fin.ext hab)

/-- The two prefix embeddings into the full finite structure
strictly commute with each n→n+1 transition. -/
theorem prefixToFinal_step {X : Type w} (m n : ℕ) (hn : n < m)
    (x : PrefixCarrier X m n) :
    prefixToFinal (X := X) m (n+1)
      (prefixStep m n hn x) = prefixToFinal m n x := by
  cases x with
  | inl a => rfl
  | inr i => apply congrArg Sum.inr; apply Fin.ext; rfl

/-- The unique vertex added when n < m. -/
def prefixFresh {X : Type w} (m n : ℕ) (hn : n < m) :
    PrefixCarrier X m (n+1) :=
  Sum.inr ⟨n, by omega⟩

theorem prefixFresh_out {X : Type w} (m n : ℕ) (hn : n < m)
    (x : PrefixCarrier X m n) :
    prefixStep m n hn x ≠ prefixFresh m n hn := by
  cases x with
  | inl a =>
      simp [prefixStep, prefixFresh]
  | inr i =>
      intro heq
      have hh : i.val = n := by
        simpa only [prefixStep, prefixFresh,
          Sum.inr.injEq, Fin.mk.injEq] using heq
      have hi := i.isLt
      omega

/-- All vertices in the next prefix are old or the single fresh
index n. This also certifies that no phantom vertices appear. -/
theorem prefixStep_cover {X : Type w} (m n : ℕ) (hn : n < m)
    (y : PrefixCarrier X m (n+1)) :
    y = prefixFresh m n hn ∨
      ∃ x : PrefixCarrier X m n, prefixStep m n hn x = y := by
  cases y with
  | inl a =>
      right
      exact ⟨Sum.inl a, rfl⟩
  | inr j =>
      by_cases hj : j.val < min n m
      · right
        refine ⟨Sum.inr ⟨j.val, hj⟩, ?_⟩
        apply congrArg Sum.inr
        apply Fin.ext
        rfl
      · left
        have hnval : j.val = n := by
          have hjlt := j.isLt
          omega
        apply congrArg Sum.inr
        apply Fin.ext
        exact hnval

/-- The original relational structure induced on the n-prefix. -/
def prefixStructure {X : Type w} {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (n : ℕ) :
    Structure (rectangleLanguage C) (PrefixCarrier X m n) :=
  pullbackRectangle P (prefixToFinal m n)

/-- One successor of the induced finite prefix chain is a genuine
original E/R_c embedding (not merely preservation of effective G). -/
def prefixStructure_step {X : Type w} {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (n : ℕ) (hn : n < m) :
    Structure.Embedding (rectangleTrivialAction C)
      (prefixStructure P n) (prefixStructure P (n+1)) := by
  let f : PrefixCarrier X m n → PrefixCarrier X m (n+1) :=
    prefixStep m n hn
  have he : ∀ x : PrefixCarrier X m n,
      prefixToFinal m (n+1) (f x) = prefixToFinal m n x :=
    prefixToFinal_step m n hn
  apply embeddingOfPairwiseEquiv (rectangleTrivialAction C)
    (prefixStructure P n) (prefixStructure P (n+1))
    f (prefixStep_injective m n hn)
  · intro x y
    simp only [prefixStructure, pullback_partRel, he x, he y]
  · intro c x y
    simp only [prefixStructure, pullback_rawRel, he x, he y]

/-- Every arbitrary finite original R1--R3 structure on
X ⊕ Fin m canonically yields an honest *finite* one-point
chain of length exactly m. This is an actual construction,
not an assumption of an existing Fraïssé limit. -/
noncomputable def finitePrefixOnePointChain
    {X : Type (max u v)} [Fintype X] {m : ℕ}
    (P : Structure (rectangleLanguage C) (X ⊕ Fin m))
    (hP : IsRectangleStructure d P) :
    FiniteRelationalOnePointChain d
      (fun n => PrefixCarrier X m n) where
  length := m
  stage := prefixStructure P
  valid := fun n => hP.pullback (prefixToFinal m n)
  step := fun n hn => prefixStructure_step P n hn
  fresh := fun n hn => prefixFresh m n hn
  fresh_out := fun n hn x => prefixFresh_out m n hn x
  cover := fun n hn x => prefixStep_cover m n hn x

end SemigenericEPPA
