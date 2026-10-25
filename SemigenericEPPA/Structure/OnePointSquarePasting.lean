import SemigenericEPPA.Structure.RelativeOnePointSAP
import SemigenericEPPA.Structure.StrongSquare
import SemigenericEPPA.Structure.PairwiseEmbedding
import SemigenericEPPA.Bridge.RawTypedEPPA

/-!
# Extending an exact strong square by one further vertex

Suppose an exact jointly-surjective strong square amalgamates a
ONE-POINT extension B/A with an arbitrary finite extension C/A.
Then the amalgam D is itself a one-point extension of C: its unique
new vertex is the image of B's distinguished new vertex.

If E/C is a further one-point extension, the existing certified
relative one-point SAP theorem therefore amalgamates D and E over C.
Pasting that square with the given B--C square produces an exact
strong square for B and E over A.

This is the *local induction step* needed to iterate one-point SAP
to full finite SAP. It asserts an actual R1--R3 amalgam on a finite
carrier, uses genuine original-language structure embeddings, and
tracks exact overlap and cover; it is not yet the terminal finite-SAP
existence theorem.
-/

namespace SemigenericEPPA

open AllThoseEPPA

universe u v w x y z t

variable {G : Type u} [Group G] {C : Type v}
variable {d : RawDatum G C}

private theorem trivialLang
    {V W : Type*}
    {A : Structure (rectangleLanguage C) V}
    {B : Structure (rectangleLanguage C) W}
    (f : Structure.Embedding (rectangleTrivialAction C) A B) :
    f.lang = 1 := by
  apply Equiv.ext
  intro i
  exact Fin.elim0 i

/-- A certified one-point side of a strong square can be pasted
against one further arbitrary one-point extension of the other side.
The resulting (new) amalgam is an exact strong square, again with
genuine original-language embeddings. -/
theorem strongSquare_extend_right_onePoint
    {X : Type w} {Y : Type x} {Z : Type y}
    {T : Type z} {U : Type t}
    [Fintype Z]
    {A : Structure (rectangleLanguage C) X}
    {B : Structure (rectangleLanguage C) Y}
    {M : Structure (rectangleLanguage C) Z}
    {D : Structure (rectangleLanguage C) T}
    {E : Structure (rectangleLanguage C) U}
    (hM : IsRectangleStructure d M)
    (hD : IsRectangleStructure d D)
    (hE : IsRectangleStructure d E)
    (f : Structure.Embedding (rectangleTrivialAction C) A B)
    (g : Structure.Embedding (rectangleTrivialAction C) A M)
    (i : Structure.Embedding (rectangleTrivialAction C) B D)
    (j : Structure.Embedding (rectangleTrivialAction C) M D)
    (k : Structure.Embedding (rectangleTrivialAction C) M E)
    (hSquare : StrongSquare
      (fun a : X => f a) (fun a : X => g a)
      (fun b : Y => i b) (fun c : Z => j c))
    (freshB : Y)
    (freshB_out : ∀ a : X, f a ≠ freshB)
    (coverB : ∀ b : Y, b = freshB ∨ ∃ a : X, f a = b)
    (freshE : U)
    (freshE_out : ∀ c : Z, k c ≠ freshE)
    (coverE : ∀ e : U, e = freshE ∨ ∃ c : Z, k c = e) :
    ∃ S : Structure (rectangleLanguage C) (TwoPointCarrier Z),
      IsRectangleStructure d S ∧
      ∃ (p : Structure.Embedding (rectangleTrivialAction C) D S)
        (q : Structure.Embedding (rectangleTrivialAction C) E S),
        StrongSquare
          (fun a : X => f a)
          (fun a : X => k (g a))
          (fun b : Y => p (i b))
          (fun e : U => q e) := by
  classical
  have freshD_out : ∀ c : Z, j c ≠ i freshB := by
    intro c hc
    obtain ⟨a, hOld, _⟩ :=
      (hSquare.exact_overlap freshB c).mp hc.symm
    exact freshB_out a hOld.symm
  have coverD : ∀ d : T, d = i freshB ∨ ∃ c : Z, j c = d := by
    intro dd
    rcases hSquare.jointly_surjective dd with ⟨b, hb⟩ | ⟨c, hc⟩
    · rcases coverB b with hFresh | ⟨a, hOld⟩
      · left
        calc
          dd = i b := hb.symm
          _ = i freshB := congrArg i hFresh
      · right
        refine ⟨g a, ?_⟩
        calc
          j (g a) = i (f a) := (hSquare.commute a).symm
          _ = i b := congrArg i hOld
          _ = dd := hb
    · exact Or.inr ⟨c, hc⟩
  let Q : RelativeOnePointDiagram d Z T U := {
    base := M
    left := D
    right := E
    baseValid := hM
    leftValid := hD
    rightValid := hE
    leftOld := j
    rightOld := k
    leftInjective := j.injective
    rightInjective := k.injective
    leftFresh := i freshB
    rightFresh := freshE
    leftFreshOutside := freshD_out
    rightFreshOutside := freshE_out
    leftCover := coverD
    rightCover := coverE
    leftPart := by
      intro a b
      exact embedding_part_iff (rectangleTrivialAction C)
        M D j (trivialLang j) a b
    rightPart := by
      intro a b
      exact embedding_part_iff (rectangleTrivialAction C)
        M E k (trivialLang k) a b
    leftRaw := by
      intro c a b
      exact embedding_raw_iff (rectangleTrivialAction C)
        M D j (trivialLang j) c a b
    rightRaw := by
      intro c a b
      exact embedding_raw_iff (rectangleTrivialAction C)
        M E k (trivialLang k) c a b
  }
  obtain ⟨S, hS, p, q, hOldP, hOldQ,
    _hFreshP, _hFreshQ, hOverlap, hCover⟩ :=
    Q.finite_relative_onePoint_strong_amalgamation
      (rectangleTrivialAction C)
  have hNext : StrongSquare
      (fun c : Z => j c) (fun c : Z => k c)
      (fun t : T => p t) (fun u : U => q u) := by
    refine ⟨?_, ?_, hCover⟩
    · intro c
      exact (hOldP c).trans (hOldQ c).symm
    · intro t u
      exact hOverlap t u
  refine ⟨S, hS, p, q, ?_⟩
  exact StrongSquare.paste hSquare hNext

end SemigenericEPPA
