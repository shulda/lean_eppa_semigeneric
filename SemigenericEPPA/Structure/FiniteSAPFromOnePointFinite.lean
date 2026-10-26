import SemigenericEPPA.Structure.OnePointChainSAP
import SemigenericEPPA.Structure.StrongSquare

/-!
# Iterating relative one-point vs finite SAP along any finite chain

We isolate the exact FINAL induction step needed for full finite SAP.
Assume the following local relative extension statement:

  Any one-point extension B/A strongly amalgamates with ANY finite
  original-relational extension D/A, over the given induced maps.

Then, by induction on a genuine finite one-point chain
A = B₀ ↪ B₁ ↪ ... ↪ Bₙ, EVERY Bₙ strongly amalgamates with an
arbitrary fixed finite C/A. Exact overlap and joint surjectivity
are retained by certified StrongSquare.paste.

The local hypothesis is deliberately explicit, NOT silently
asserted from one-point-vs-one-point SAP. Its discharge via
finite normalization and the already certified finite-chain
construction is the remaining step toward unconditional full SAP.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v

variable {G : Type u} [Group G] {C : Type v} {d : RawDatum G C}

/-- The precise local one-point-versus-arbitrary-finite
strong-amalgamation statement for original relational structures
and genuine identity-language embeddings.

This predicate is a temporary intermediate interface, not an
additional assumption in the intended unconditional SAP theorem. -/
def HasOnePointAgainstFiniteStrongSAP (d : RawDatum G C) : Prop :=
  ∀ {X Y Z : Type (max u v)}
    [Fintype X] [Fintype Y] [Fintype Z]
    {A : Structure (rectangleLanguage C) X}
    {B : Structure (rectangleLanguage C) Y}
    {D : Structure (rectangleLanguage C) Z},
    IsRectangleStructure d A →
    IsRectangleStructure d B →
    IsRectangleStructure d D →
    ∀ (f : Structure.Embedding (rectangleTrivialAction C) A B)
      (g : Structure.Embedding (rectangleTrivialAction C) A D)
      (fresh : Y),
      (∀ x : X, f x ≠ fresh) →
      (∀ y : Y, y = fresh ∨ ∃ x : X, f x = y) →
      ∃ (W : Type (max u v)) (hW : Fintype W)
        (S : Structure (rectangleLanguage C) W),
        IsRectangleStructure d S ∧
        ∃ (p : Structure.Embedding (rectangleTrivialAction C) B S)
          (q : Structure.Embedding (rectangleTrivialAction C) D S),
          StrongSquare
            (fun x : X => f x) (fun x : X => g x)
            (fun y : Y => p y) (fun z : Z => q z)

namespace FiniteRelationalOnePointChain

variable {V : ℕ → Type (max u v)} [∀ n, Fintype (V n)]
variable (T : FiniteRelationalOnePointChain d V)

/-- Iterating the local one-point-versus-finite property along
an arbitrary finite one-point chain gives genuine strong
amalgamation of its final prefix against ANY prescribed finite
original-language extension of the initial stage.

All intermediate maps preserve/reflect E and each ordered R_c.
The output strong square includes exact overlap AND covering.
This is NOT a proof of the local hypothesis. -/
theorem amalgamate_chain_against_finite
    (hSAP : HasOnePointAgainstFiniteStrongSAP d)
    {Z : Type (max u v)} [Fintype Z]
    (C₀ : Structure (rectangleLanguage C) Z)
    (hC : IsRectangleStructure d C₀)
    (g₀ : Structure.Embedding (rectangleTrivialAction C)
      (T.stage 0) C₀) :
    ∀ n : ℕ, n ≤ T.length →
      ∃ (W : Type (max u v)) (hW : Fintype W)
        (D : Structure (rectangleLanguage C) W),
        IsRectangleStructure d D ∧
        ∃ (f : Structure.Embedding (rectangleTrivialAction C)
          (T.stage 0) (T.stage n))
          (i : Structure.Embedding (rectangleTrivialAction C)
            (T.stage n) D)
          (j : Structure.Embedding (rectangleTrivialAction C)
            C₀ D),
          StrongSquare
            (fun x : V 0 => f x)
            (fun x : V 0 => g₀ x)
            (fun b : V n => i b)
            (fun c : Z => j c) := by
  classical
  intro n
  induction n with
  | zero =>
      intro _hn
      let f : Structure.Embedding (rectangleTrivialAction C)
          (T.stage 0) (T.stage 0) :=
        Structure.Embedding.id (T.stage 0)
      let j : Structure.Embedding (rectangleTrivialAction C)
          C₀ C₀ := Structure.Embedding.id C₀
      refine ⟨Z, inferInstance, C₀, hC, f, g₀, j, ?_⟩
      exact StrongSquare.identity_left (fun x : V 0 => g₀ x)
  | succ n ih =>
      intro hn
      have hlt : n < T.length := Nat.lt_of_succ_le hn
      obtain ⟨W, hW, D, hD, f, i, j, hSquare⟩ :=
        ih (Nat.le_of_lt hlt)
      letI : Fintype W := hW
      obtain ⟨U, hU, S, hS, p, q, hNext⟩ :=
        hSAP (T.valid n) (T.valid (n + 1)) hD
          (T.step n hlt) i
          (T.fresh n hlt) (T.fresh_out n hlt) (T.cover n hlt)
      refine ⟨U, hU, S, hS,
        (T.step n hlt).comp f, p, q.comp j, ?_⟩
      exact ((StrongSquare.paste hSquare.swap hNext.swap).swap)

end FiniteRelationalOnePointChain
end SemigenericEPPA
