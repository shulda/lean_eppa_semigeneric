import SemigenericEPPA.Structure.OnePointChainSAP

/-!
# Strict prescribed base maps in one-point-chain amalgamation

A finite one-point chain has a *specified* sequence of old embeddings.
Its canonical from-zero embedding is the literal composite of these
stage embeddings. When amalgamating one external one-point extension
against the entire chain, the common-base map in the final exact
strong square is precisely this prescribed composite, not some
unspecified embedding of an isomorphic structure.

This strengthens the earlier existential chain result, and is the
exact map-compatibility gate required before transporting the
canonical SAP argument back to arbitrary finite input diagrams.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type (max u v)} [∀ n, Fintype (V n)]

namespace FiniteRelationalOnePointChain

/-- Prescribed inclusion of stage zero into a particular
finite chain prefix. It is literally the ordered composition
of all old vertex embeddings; no choice of isomorphic copy. -/
def fromZero
    (T : FiniteRelationalOnePointChain d V) :
    ∀ (n : ℕ), n ≤ T.length →
      Structure.Embedding (rectangleTrivialAction C)
        (T.stage 0) (T.stage n)
  | 0, _ => Structure.Embedding.id (T.stage 0)
  | n+1, hn =>
      (T.step n (Nat.lt_of_succ_le hn)).comp
        (T.fromZero n (Nat.le_of_lt (Nat.lt_of_succ_le hn)))

/-- A prescribed one-point extension B of the initial stage
amalgamates strongly with any chain prefix, and the copy of
the initial stage in the final square is exactly T.fromZero.
All original ordered E/R_c predicates are reflected, and all
amalgam vertices are covered by the two images. -/
theorem amalgamate_onePoint_against_chain_exact
    (T : FiniteRelationalOnePointChain d V)
    {Y : Type (max u v)} [Fintype Y]
    (B : Structure (rectangleLanguage C) Y)
    (hB : IsRectangleStructure d B)
    (f : Structure.Embedding (rectangleTrivialAction C)
      (T.stage 0) B)
    (freshB : Y)
    (freshB_out : ∀ x : V 0, f x ≠ freshB)
    (coverB : ∀ b : Y, b = freshB ∨ ∃ x : V 0, f x = b) :
    ∀ (n : ℕ) (hn : n ≤ T.length),
      ∃ (W : Type (max u v)) (hW : Fintype W)
        (D : Structure (rectangleLanguage C) W),
        IsRectangleStructure d D ∧
        ∃ (i : Structure.Embedding (rectangleTrivialAction C) B D)
          (j : Structure.Embedding (rectangleTrivialAction C)
            (T.stage n) D),
          StrongSquare
            (fun x : V 0 => f x)
            (fun x : V 0 => T.fromZero n hn x)
            (fun b : Y => i b)
            (fun c : V n => j c) := by
  classical
  intro n
  induction n with
  | zero =>
      intro _hn
      let i : Structure.Embedding (rectangleTrivialAction C) B B :=
        Structure.Embedding.id B
      refine ⟨Y, inferInstance, B, hB, i, f, ?_⟩
      exact StrongSquare.identity_right (fun x : V 0 => f x)
  | succ n ih =>
      intro hn
      have hlt : n < T.length := Nat.lt_of_succ_le hn
      let hprev : n ≤ T.length := Nat.le_of_lt hlt
      obtain ⟨W, hW, D, hD, i, j, hSq⟩ := ih hprev
      letI : Fintype W := hW
      obtain ⟨S, hS, p, q, hNext⟩ :=
        strongSquare_extend_right_onePoint
          (d := d)
          (T := W)
          (hM := T.valid n) (hD := hD) (hE := T.valid (n+1))
          f (T.fromZero n hprev) i j (T.step n hlt) hSq
          freshB freshB_out coverB
          (T.fresh n hlt) (T.fresh_out n hlt) (T.cover n hlt)
      refine ⟨TwoPointCarrier (V n), inferInstance, S, hS,
        p.comp i, q, ?_⟩
      exact hNext

end FiniteRelationalOnePointChain
end SemigenericEPPA
