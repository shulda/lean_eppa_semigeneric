import SemigenericEPPA.Bridge.DLFDeltaProfileInvolutionCrossing

/-!
# Delta-profile forcing WITHOUT a fixed third point

The negative DLF proof needs to eliminate every nontrivial
involution preserving E-classes setwise, including a product of
disjoint transpositions with NO fixed point in the moved class.

The previous 3+1 geometry fixed a third old point c. Here we
instead compare the columns a and T(c). If T(b)=a and b E c,
literal E-preservation gives a E T(c), whether or not T(c)=c.

For a vertex v in a different E-class, assume its effective
profile takes the value delta≠1 at a and the identity at b, c,
and T(c). If v E T(v), the two rows v,T(v) and columns a,T(c)
have effective colours
  [[delta,1],[1,1]],
contradicting the rank-one rectangle equation.

The later singleton-one-point extension can arrange the fourth
profile equality automatically by putting phi(f(x))=1 for ALL
old x other than a. No distinguished fixed c is needed.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {W : Type w} {d : RawDatum G C}

/-- Preservation of the exact Option-valued raw colour forces
preservation and reflection of the E relation. -/
theorem RawRectanglePresentation.part_iff_of_colourEquivariant
    (P : RawRectanglePresentation d W)
    (T : Equiv.Perm W)
    (hTcolour : ∀ x y : W, P.colour (T x) (T y) = P.colour x y)
    (x y : W) :
    P.part (T x) (T y) ↔ P.part x y := by
  constructor
  · intro hxy
    have hc : P.colour (T x) (T y) = none :=
      (P.colour_none_iff (T x) (T y)).mpr hxy
    rw [hTcolour x y] at hc
    exact (P.colour_none_iff x y).mp hc
  · intro hxy
    have hc : P.colour x y = none :=
      (P.colour_none_iff x y).mpr hxy
    apply (P.colour_none_iff (T x) (T y)).mp
    rw [hTcolour x y]
    exact hc

/-- An asymmetric delta profile forces v and Tv into different
E-classes, with NO assumption that T fixes the third old vertex
c (and NO need for T to be an involution).

The fourth value F(v,Tc)=1 is the exact extra profile datum
supplied by a singleton extension whose only exceptional column
is a. -/
theorem RawRectanglePresentation.deltaProfile_forces_crossPart_movingThird
    (P : RawRectanglePresentation d W)
    (T : Equiv.Perm W)
    (hTcolour : ∀ x y : W, P.colour (T x) (T y) = P.colour x y)
    (a b c v : W)
    (hbc : P.part b c)
    (hva : ¬P.part v a)
    (hTb : T b = a)
    (delta : G) (hdelta : delta ≠ 1)
    (hvaF : P.effectiveReduct.F v a = delta)
    (hvbF : P.effectiveReduct.F v b = 1)
    (hvcF : P.effectiveReduct.F v c = 1)
    (hvTcF : P.effectiveReduct.F v (T c) = 1) :
    ¬P.part v (T v) := by
  classical
  intro hvw
  let D : EffectiveGeometry d.s W := P.effectiveReduct
  have hvwD : D.part v (T v) :=
    (P.effectiveReduct_part v (T v)).mpr hvw
  have hbcT : P.part (T b) (T c) :=
    (P.part_iff_of_colourEquivariant T hTcolour b c).mpr hbc
  have hac : P.part a (T c) := by
    rw [hTb] at hbcT
    exact hbcT
  have hacD : D.part a (T c) :=
    (P.effectiveReduct_part a (T c)).mpr hac
  have hvaD : ¬D.part v a := by
    intro h
    exact hva ((P.effectiveReduct_part v a).mp h)
  obtain ⟨_hvTcCross, hwacross, hwTccross⟩ :=
    D.cross_square v (T v) a (T c) hvwD hacD hvaD
  have hrawWa : P.colour (T v) a = P.colour v b := by
    calc
      P.colour (T v) a = P.colour (T v) (T b) := by rw [hTb]
      _ = P.colour v b := hTcolour v b
  have hWaCross : ¬P.part (T v) a := by
    intro h
    exact hwacross ((P.effectiveReduct_part (T v) a).mpr h)
  have hWTcCross : ¬P.part (T v) (T c) := by
    intro h
    exact hwTccross ((P.effectiveReduct_part (T v) (T c)).mpr h)
  have hWa : D.F (T v) a = 1 :=
    (P.effectiveReduct_equalColour (T v) a v b hrawWa hWaCross).trans hvbF
  have hWTc : D.F (T v) (T c) = 1 :=
    (P.effectiveReduct_equalColour
      (T v) (T c) v c (hTcolour v c) hWTcCross).trans hvcF
  have hrect := D.rectangle v (T v) a (T c) hvwD hacD hvaD
  have hinv : delta⁻¹ = 1 := by
    change (P.effectiveReduct.F v a)⁻¹ *
        P.effectiveReduct.F v (T c) =
      (P.effectiveReduct.F (T v) a)⁻¹ *
        P.effectiveReduct.F (T v) (T c) at hrect
    rw [hvaF, hvTcF, hWa, hWTc] at hrect
    simpa only [mul_one, inv_one] using hrect
  have hcontra : delta = 1 := by
    have h := congrArg (fun x : G => x⁻¹) hinv
    simpa only [inv_inv, inv_one] using h
  exact hdelta hcontra

/-- A locally complete-orbit-safe involution cannot preserve this
asymmetric profile even if its third old vertex c is moved.
This makes the negative DLF proof independent of fixed points
inside nontrivially permuted E-classes. -/
theorem RawRectanglePresentation.noSafeDeltaProfileInvolution_movingThird
    (P : RawRectanglePresentation d W)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (T : Equiv.Perm W)
    (hTcolour : ∀ x y : W, P.colour (T x) (T y) = P.colour x y)
    (hTtwo : ∀ x : W, T (T x) = x)
    (hSafe : ∀ x y : W, ¬P.part x y →
      T x = y → T y = x →
        d.GoodCompleteOrbitAt (P.effectiveReduct.F x y))
    (a b c v : W)
    (hbc : P.part b c)
    (hva : ¬P.part v a)
    (hTb : T b = a)
    (delta : G) (hdelta : delta ≠ 1)
    (hvaF : P.effectiveReduct.F v a = delta)
    (hvbF : P.effectiveReduct.F v b = 1)
    (hvcF : P.effectiveReduct.F v c = 1)
    (hvTcF : P.effectiveReduct.F v (T c) = 1) :
    False := by
  have hCross : ¬P.part v (T v) :=
    P.deltaProfile_forces_crossPart_movingThird T hTcolour
      a b c v hbc hva hTb delta hdelta hvaF hvbF hvcF hvTcF
  have hGood : d.GoodCompleteOrbitAt
      (P.effectiveReduct.F v (T v)) :=
    hSafe v (T v) hCross rfl (hTtwo v)
  exact hNoOrbit
    ((d.hasCompleteGoodOrbit_iff_exists_goodCompleteOrbitAt).2
      ⟨P.effectiveReduct.F v (T v), hGood⟩)

end SemigenericEPPA
