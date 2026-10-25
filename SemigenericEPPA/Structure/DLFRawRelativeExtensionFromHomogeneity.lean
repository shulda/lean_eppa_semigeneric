import SemigenericEPPA.Structure.DLFFullRawAutomorphismGroup
import SemigenericEPPA.Structure.RawPresentation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Original-language relative age extension from universality and homogeneity

If an original raw E/R_c structure M contains induced copies of
each finite original raw rectangle and every finite induced partial
isomorphism of M extends to an ACTUAL raw automorphism of M, then
every finite relative age diagram A→B can be embedded over ANY
prescribed existing induced embedding A→M.

Proof: choose an arbitrary induced copy B→M by age universality.
On its finite A-image, the inverse of the A-embedding followed by
the desired copy of A is a literal partial raw automorphism of M.
Homogeneity extends this partial map to an automorphism α; compose
α with the chosen B→M embedding.

Crucially all maps preserve and REFLECT E and every ordered raw
Option C-colour. No effective group gauge or SAP shortcut is used.

This is the Fraïssé extension-property bridge required by the
negative DLF delta-profile obstruction: first prescribe the old
finite invariant action, then embed the killer extension OVER it.
-/

namespace SemigenericEPPA

universe u v w t z
variable {G : Type u} [Group G] {C : Type v}
variable {A : Type w} {B : Type t} {X : Type z}
variable {d : RawDatum G C}

namespace RawRectanglePresentation

/-- Given a finite induced embedding A→B, a prescribed induced copy
of A in M, and SOME induced copy of B in M, full finite-partial-map
homogeneity of M permits replacing that B copy by one whose
restriction to A is EXACTLY the prescribed old embedding.

One can supply a B copy obtained from finite age universality; the
theorem does not assume B carries any action of the old subgroup. -/
theorem relative_embedding_of_age_and_homogeneity
    [Fintype A]
    (P : RawRectanglePresentation d A)
    (Q : RawRectanglePresentation d B)
    (M : RawRectanglePresentation d X)
    (e : A → B)
    (heinj : Function.Injective e)
    (hepart : ∀ x y : A, Q.part (e x) (e y) ↔ P.part x y)
    (hecolour : ∀ x y : A, Q.colour (e x) (e y) = P.colour x y)
    (a : A → X)
    (hainj : Function.Injective a)
    (hapart : ∀ x y : A, M.part (a x) (a y) ↔ P.part x y)
    (hacolour : ∀ x y : A, M.colour (a x) (a y) = P.colour x y)
    (t : B → X)
    (htinj : Function.Injective t)
    (htpart : ∀ x y : B, M.part (t x) (t y) ↔ Q.part x y)
    (htcolour : ∀ x y : B, M.colour (t x) (t y) = Q.colour x y)
    (hHom : ∀ (F : Finset X) (p : F → X),
      Function.Injective p →
      (∀ x y : F, M.part (p x) (p y) ↔ M.part x.val y.val) →
      (∀ x y : F, M.colour (p x) (p y) =
        M.colour x.val y.val) →
      ∃ α : M.fullRawAutGroup,
        ∀ x : F, α.val x.val = p x) :
    ∃ b : B → X,
      Function.Injective b ∧
      (∀ x y : B, M.part (b x) (b y) ↔ Q.part x y) ∧
      (∀ x y : B, M.colour (b x) (b y) = Q.colour x y) ∧
      (∀ x : A, b (e x) = a x) := by
  classical
  let g : A → X := fun x => t (e x)
  have hginj : Function.Injective g := htinj.comp heinj
  let F : Finset X := Finset.univ.image g
  have hWitness (z : F) : ∃ x : A, g x = z.val := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp z.property
    exact ⟨x, hx⟩
  let inv : F → A := fun z => Classical.choose (hWitness z)
  have hinv (z : F) : g (inv z) = z.val :=
    Classical.choose_spec (hWitness z)
  let p : F → X := fun z => a (inv z)
  have hpInj : Function.Injective p := by
    intro x y hxy
    have hix : inv x = inv y := hainj hxy
    apply Subtype.ext
    calc
      x.val = g (inv x) := (hinv x).symm
      _ = g (inv y) := congrArg g hix
      _ = y.val := hinv y
  have hpPart : ∀ x y : F,
      M.part (p x) (p y) ↔ M.part x.val y.val := by
    intro x y
    change M.part (a (inv x)) (a (inv y)) ↔
      M.part x.val y.val
    calc
      M.part (a (inv x)) (a (inv y)) ↔
          P.part (inv x) (inv y) := hapart (inv x) (inv y)
      _ ↔ Q.part (e (inv x)) (e (inv y)) :=
        (hepart (inv x) (inv y)).symm
      _ ↔ M.part (t (e (inv x))) (t (e (inv y))) :=
        (htpart (e (inv x)) (e (inv y))).symm
      _ ↔ M.part x.val y.val := by
        change M.part (g (inv x)) (g (inv y)) ↔
          M.part x.val y.val
        rw [hinv x, hinv y]
  have hpColour : ∀ x y : F,
      M.colour (p x) (p y) = M.colour x.val y.val := by
    intro x y
    change M.colour (a (inv x)) (a (inv y)) =
      M.colour x.val y.val
    calc
      M.colour (a (inv x)) (a (inv y)) =
          P.colour (inv x) (inv y) := hacolour (inv x) (inv y)
      _ = Q.colour (e (inv x)) (e (inv y)) :=
        (hecolour (inv x) (inv y)).symm
      _ = M.colour (t (e (inv x))) (t (e (inv y))) :=
        (htcolour (e (inv x)) (e (inv y))).symm
      _ = M.colour x.val y.val := by
        change M.colour (g (inv x)) (g (inv y)) =
          M.colour x.val y.val
        rw [hinv x, hinv y]
  obtain ⟨α, hα⟩ := hHom F p hpInj hpPart hpColour
  refine ⟨fun x => α.val (t x), α.val.injective.comp htinj, ?_, ?_, ?_⟩
  · intro x y
    exact (M.fullRawAutGroup_part α (t x) (t y)).trans (htpart x y)
  · intro x y
    exact (M.fullRawAutGroup_colour α (t x) (t y)).trans (htcolour x y)
  · intro x
    let z : F := ⟨g x, Finset.mem_image.mpr
      ⟨x, Finset.mem_univ _, rfl⟩⟩
    have hzx : inv z = x := hginj (hinv z)
    have ha := hα z
    change α.val (g x) = a (inv z) at ha
    calc
      α.val (t (e x)) = α.val (g x) := rfl
      _ = a (inv z) := ha
      _ = a x := congrArg a hzx

end RawRectanglePresentation
end SemigenericEPPA
