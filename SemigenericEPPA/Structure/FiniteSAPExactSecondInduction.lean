import SemigenericEPPA.Structure.FiniteSAPFromOnePointFinite
import SemigenericEPPA.Structure.FiniteChainExactBaseMap

/-!
# Exact second induction for full finite R1--R3 strong amalgamation

Given the one-point-vs-ANY-finite SAP property, we amalgamate
an ENTIRE genuinely specified one-point chain against another
arbitrary finite original R1--R3 extension of its initial stage.

The old-base map is not existentially chosen: it is literally
the ordered composite T.fromZero of all given stage embeddings.
Each iteration uses StrongSquare.paste/swap and hence retains
the exact intersection and jointly-surjective carrier condition.

This complements the certified abstract proof of
FiniteRelationalOnePointChain.amalgamate_chain_against_finite:
the present strengthening fixes the exact base map needed for
transport back to the user-specified finite amalgamation span.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v
variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}
variable {V : ℕ → Type (max u v)} [∀ n, Fintype (V n)]

namespace FiniteRelationalOnePointChain

/-- Every finite chain stage strongly amalgamates with a given
arbitrary finite extension of stage 0, using the ACTUAL composed
chain map. All embeddings and exact strong-overlap conditions
are expressed in the original binary E/R_c language. -/
theorem amalgamate_chain_against_finite_exact
    (T : FiniteRelationalOnePointChain d V)
    (hSAP : HasOnePointAgainstFiniteStrongSAP d)
    {Z : Type (max u v)} [Fintype Z]
    (C₀ : Structure (rectangleLanguage C) Z)
    (hC : IsRectangleStructure d C₀)
    (g₀ : Structure.Embedding (rectangleTrivialAction C)
      (T.stage 0) C₀) :
    ∀ (n : ℕ) (hn : n ≤ T.length),
      ∃ (W : Type (max u v)) (hW : Fintype W)
        (D : Structure (rectangleLanguage C) W),
        IsRectangleStructure d D ∧
        ∃ (i : Structure.Embedding (rectangleTrivialAction C)
            (T.stage n) D)
          (j : Structure.Embedding (rectangleTrivialAction C)
            C₀ D),
          StrongSquare
            (fun x : V 0 => T.fromZero n hn x)
            (fun x : V 0 => g₀ x)
            (fun b : V n => i b)
            (fun c : Z => j c) := by
  classical
  intro n
  induction n with
  | zero =>
      intro _hn
      let j : Structure.Embedding (rectangleTrivialAction C)
          C₀ C₀ := Structure.Embedding.id C₀
      refine ⟨Z, inferInstance, C₀, hC, g₀, j, ?_⟩
      exact StrongSquare.identity_left (fun x : V 0 => g₀ x)
  | succ n ih =>
      intro hn
      have hlt : n < T.length := Nat.lt_of_succ_le hn
      have hprev : n ≤ T.length := Nat.le_of_lt hlt
      obtain ⟨W, hW, D, hD, i, j, hSquare⟩ := ih hprev
      letI : Fintype W := hW
      obtain ⟨U, hU, S, hS, p, q, hNext⟩ :=
        hSAP (T.valid n) (T.valid (n+1)) hD
          (T.step n hlt) i
          (T.fresh n hlt) (T.fresh_out n hlt) (T.cover n hlt)
      refine ⟨U, hU, S, hS, p, q.comp j, ?_⟩
      exact ((StrongSquare.paste hSquare.swap hNext.swap).swap)

end FiniteRelationalOnePointChain
end SemigenericEPPA
