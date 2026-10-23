import SemigenericEPPA.Bridge.NoGoodColourInvolutionProfile
import SemigenericEPPA.Algebra.DLFCompleteGoodOrbitTransport

/-!
# Delta-profile forcing for the negative DLF direction

The existing three-plus-one raw involution obstruction can be
strengthened before invoking the absence of self-reversing raw
colours: the asymmetric profile (delta,1,1) itself forces the
distinguished new vertex v to be sent to a DIFFERENT E-class.
No assumption on the good colour palette is needed.

Consequently, if no complete affine congruence orbit is good,
such an involution cannot be locally safe, even if there are
individual self-reversing raw colours in incomplete orbits.

This is the geometric obstruction step only. Constructing the
required delta-profile one-point extension over any given finite
action pair and composing it with the orbit killer and finite
parity argument remain separate tasks.
-/

namespace SemigenericEPPA

universe u v w
variable {G : Type u} [Group G] {C : Type v}
variable {W : Type w} {d : RawDatum G C}

/-- A raw-colour-preserving permutation sending b to a and fixing
c cannot send v into its old E-class when the old effective
profile from v to (a,b,c) is (delta,1,1), with delta ≠ 1
and a E c. This does NOT require involutivity or a good raw colour. -/
theorem RawRectanglePresentation.deltaProfile_forces_crossPart
    (Q : RawRectanglePresentation d W)
    (T : Equiv.Perm W)
    (hTcolour : ∀ x y : W, Q.colour (T x) (T y) = Q.colour x y)
    (a b c v : W)
    (hac : Q.part a c)
    (hva : ¬Q.part v a)
    (hTb : T b = a)
    (hTc : T c = c)
    (delta : G)
    (hdelta : delta ≠ 1)
    (hvaF : Q.effectiveReduct.F v a = delta)
    (hvbF : Q.effectiveReduct.F v b = 1)
    (hvcF : Q.effectiveReduct.F v c = 1) :
    ¬Q.part v (T v) := by
  classical
  intro hvw
  let D : EffectiveGeometry d.s W := Q.effectiveReduct
  have hvwD : D.part v (T v) :=
    (Q.effectiveReduct_part v (T v)).mpr hvw
  have hacD : D.part a c :=
    (Q.effectiveReduct_part a c).mpr hac
  have hvaD : ¬D.part v a := by
    intro h
    exact hva ((Q.effectiveReduct_part v a).mp h)
  obtain ⟨_hvcCross, hwacross, hwccross⟩ :=
    D.cross_square v (T v) a c hvwD hacD hvaD
  have hrawWa :
      Q.colour (T v) a = Q.colour v b := by
    calc
      Q.colour (T v) a = Q.colour (T v) (T b) := by rw [hTb]
      _ = Q.colour v b := hTcolour v b
  have hrawWc :
      Q.colour (T v) c = Q.colour v c := by
    calc
      Q.colour (T v) c = Q.colour (T v) (T c) := by rw [hTc]
      _ = Q.colour v c := hTcolour v c
  have hQa : ¬Q.part (T v) a := by
    intro h
    exact hwacross ((Q.effectiveReduct_part (T v) a).mpr h)
  have hQc : ¬Q.part (T v) c := by
    intro h
    exact hwccross ((Q.effectiveReduct_part (T v) c).mpr h)
  have hWa : D.F (T v) a = 1 :=
    (Q.effectiveReduct_equalColour (T v) a v b hrawWa hQa).trans hvbF
  have hWc : D.F (T v) c = 1 :=
    (Q.effectiveReduct_equalColour (T v) c v c hrawWc hQc).trans hvcF
  have hrect := D.rectangle v (T v) a c hvwD hacD hvaD
  have hinv : delta⁻¹ = 1 := by
    change (Q.effectiveReduct.F v a)⁻¹ *
        Q.effectiveReduct.F v c =
      (Q.effectiveReduct.F (T v) a)⁻¹ *
        Q.effectiveReduct.F (T v) c at hrect
    rw [hvaF, hvcF, hWa, hWc] at hrect
    simpa only [mul_one, inv_one] using hrect
  have hcontra : delta = 1 := by
    have h := congrArg (fun x : G => x⁻¹) hinv
    simpa only [inv_inv, inv_one] using h
  exact hdelta hcontra

/-- Under the absence of ANY complete good congruence orbit,
the delta-profile forced cross-part swap contradicts local
safety of an actual raw involution. -/
theorem RawRectanglePresentation.noSafeDeltaProfileInvolution
    (Q : RawRectanglePresentation d W)
    (hNoOrbit : ¬d.HasCompleteGoodOrbit)
    (T : Equiv.Perm W)
    (hTcolour : ∀ x y : W, Q.colour (T x) (T y) = Q.colour x y)
    (hTtwo : ∀ x : W, T (T x) = x)
    (hSafe : ∀ x y : W, ¬Q.part x y →
      T x = y → T y = x →
        d.GoodCompleteOrbitAt (Q.effectiveReduct.F x y))
    (a b c v : W)
    (hac : Q.part a c)
    (hva : ¬Q.part v a)
    (hTb : T b = a)
    (hTc : T c = c)
    (delta : G)
    (hdelta : delta ≠ 1)
    (hvaF : Q.effectiveReduct.F v a = delta)
    (hvbF : Q.effectiveReduct.F v b = 1)
    (hvcF : Q.effectiveReduct.F v c = 1) :
    False := by
  have hCross : ¬Q.part v (T v) :=
    Q.deltaProfile_forces_crossPart T hTcolour
      a b c v hac hva hTb hTc delta hdelta hvaF hvbF hvcF
  have hGood : d.GoodCompleteOrbitAt
      (Q.effectiveReduct.F v (T v)) :=
    hSafe v (T v) hCross rfl (hTtwo v)
  exact hNoOrbit
    ((d.hasCompleteGoodOrbit_iff_exists_goodCompleteOrbitAt).2
      ⟨Q.effectiveReduct.F v (T v), hGood⟩)

end SemigenericEPPA
