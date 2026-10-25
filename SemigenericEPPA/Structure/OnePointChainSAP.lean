import SemigenericEPPA.Structure.OnePointSquarePasting

/-!
# A one-point extension amalgamates strongly against a finite chain

An honest sequence of finite original R1--R3 structures, with each
successive embedding adding exactly one vertex, can be amalgamated
with a fixed one-point extension of the initial stage through a finite prefix.

At every stage we retain actual induced AllThoseEPPA embeddings and
an EXACT strong square. The induction uses the certified one-point
pasting lemma, never a bare existence claim lacking coverage.

This is an iteration spine for the full arbitrary-finite SAP proof.
Representing an arbitrary finite extension by such a chain, and
then iterating over the other side, are separate remaining steps.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

/-- A genuine sequence of finite induced original-language
extensions, each introducing exactly one genuinely fresh vertex. -/
structure FiniteRelationalOnePointChain
    (d : RawDatum G C)
    (V : ℕ → Type (max u v))
    [∀ n, Fintype (V n)] where
  length : ℕ
  stage : ∀ n, Structure (rectangleLanguage C) (V n)
  valid : ∀ n, IsRectangleStructure d (stage n)
  step : ∀ n, n < length →
    Structure.Embedding (rectangleTrivialAction C)
      (stage n) (stage (n+1))
  fresh : ∀ n, n < length → V (n+1)
  fresh_out : ∀ n (hn : n < length) (x : V n),
    step n hn x ≠ fresh n hn
  cover : ∀ n (hn : n < length) (y : V (n+1)),
    y = fresh n hn ∨ ∃ x : V n, step n hn x = y

namespace FiniteRelationalOnePointChain

variable {V : ℕ → Type (max u v)} [∀ n, Fintype (V n)]
variable (T : FiniteRelationalOnePointChain d V)

/-- Any one-point extension B of stage zero can be amalgamated
strongly with any *finite prefix* of an arbitrary one-point chain.

The selected witnessing carrier W is finite; all four sides of
the square are true induced original E/R_c embeddings. Its
images overlap exactly on the initial structure and cover W. -/
theorem amalgamate_onePoint_against_chain
    {Y : Type (max u v)} [Fintype Y]
    (B : Structure (rectangleLanguage C) Y)
    (hB : IsRectangleStructure d B)
    (f : Structure.Embedding (rectangleTrivialAction C)
      (T.stage 0) B)
    (freshB : Y)
    (freshB_out : ∀ x : V 0, f x ≠ freshB)
    (coverB : ∀ b : Y, b = freshB ∨ ∃ x : V 0, f x = b) :
    ∀ n : ℕ, n ≤ T.length →
      ∃ (W : Type (max u v)) (hW : Fintype W)
        (D : Structure (rectangleLanguage C) W),
        IsRectangleStructure d D ∧
        ∃ (g : Structure.Embedding (rectangleTrivialAction C)
            (T.stage 0) (T.stage n))
          (i : Structure.Embedding (rectangleTrivialAction C) B D)
          (j : Structure.Embedding (rectangleTrivialAction C)
            (T.stage n) D),
          StrongSquare
            (fun x : V 0 => f x)
            (fun x : V 0 => g x)
            (fun b : Y => i b)
            (fun c : V n => j c) := by
  classical
  intro n
  induction n with
  | zero =>
      intro _hn
      let e : Structure.Embedding (rectangleTrivialAction C)
          (T.stage 0) (T.stage 0) :=
        Structure.Embedding.id (T.stage 0)
      let i : Structure.Embedding (rectangleTrivialAction C) B B :=
        Structure.Embedding.id B
      refine ⟨Y, inferInstance, B, hB, e, i, f, ?_⟩
      exact StrongSquare.identity_right (fun x : V 0 => f x)
  | succ n ih =>
      intro hn
      have hlt : n < T.length := Nat.lt_of_succ_le hn
      obtain ⟨W, hW, D, hD, g, i, j, hSquare⟩ := ih (Nat.le_of_lt hlt)
      letI : Fintype W := hW
      obtain ⟨S, hS, p, q, hNewSquare⟩ :=
        strongSquare_extend_right_onePoint
          (d := d)
          (T := W)
          (hM := T.valid n) (hD := hD) (hE := T.valid (n+1))
          f g i j (T.step n hlt) hSquare
          freshB freshB_out coverB
          (T.fresh n hlt) (T.fresh_out n hlt) (T.cover n hlt)
      refine ⟨TwoPointCarrier (V n), inferInstance, S, hS,
        (T.step n hlt).comp g, p.comp i, q, ?_⟩
      exact hNewSquare

end FiniteRelationalOnePointChain
end SemigenericEPPA
