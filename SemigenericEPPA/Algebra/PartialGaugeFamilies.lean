import SemigenericEPPA.Algebra.AnchoredPartialGauge

/-!
# The full partial-map gauge multiplier family (3.14)--(3.15)

Fix an indexed gauge presentation with part map cls : V → I,
coordinates a(x,j), and skeleton K(i,j).  A partial real map p
determines a set P of *visited* part indices.  Assume its
cross-part effective colours (in the indexed-gauge formula) are
preserved and that the gauge is normalized on each diagonal,
a(x,cls(x))=1.  The latter is justified on our explicit uniformly
padded geometry by a separate theorem.

We choose one actual old-domain anchor in each visited part and define
m(i,j) using that anchor; there is no additional group-theoretic
choice.  The anchored partial gauge converse proves (3.14)
simultaneously for all old-domain points, and (3.15) for every two
distinct visited parts.  Unvisited sources are assigned a harmless
default 1; multipliers to unvisited targets are left freely chosen
by this anchor convention.

All identities retain the order of products in a noncommutative G
and use the general affine anti-involution. This is a *genuine
family*, not merely an existence claim for one ordered pair. The
subsequent E0 bridge must instantiate the colour hypothesis from
an actual partial automorphism of the padded effective geometry.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {I : Type v} {V : Type w}

/-- Concrete multiplier determined by a chosen domain anchor in the
source part. On the diagonal it is 1, and on an unvisited source
part it is also 1. -/
noncomputable def partialGaugeMultiplier
    (S : Set V) (p : S → V) (ι : Equiv.Perm I)
    (cls : V → I) (a : V → I → G)
    (i j : I) : G := by
  classical
  exact if hi : ∃ x : S, cls x.val = i then
    if i = j then 1
    else a (p (Classical.choose hi)) (ι j) *
      (a (Classical.choose hi).val j)⁻¹
  else 1

@[simp] theorem partialGaugeMultiplier_diag
    (S : Set V) (p : S → V) (ι : Equiv.Perm I)
    (cls : V → I) (a : V → I → G) (i : I) :
    partialGaugeMultiplier S p ι cls a i i = 1 := by
  classical
  simp [partialGaugeMultiplier]

theorem partialGaugeMultiplier_visited_ne
    (S : Set V) (p : S → V) (ι : Equiv.Perm I)
    (cls : V → I) (a : V → I → G)
    (i j : I)
    (hi : ∃ x : S, cls x.val = i) (hij : i ≠ j) :
    partialGaugeMultiplier S p ι cls a i j =
      a (p (Classical.choose hi)) (ι j) *
        (a (Classical.choose hi).val j)⁻¹ := by
  classical
  simp [partialGaugeMultiplier, hi, hij]

/-- Anchored group-valued cross-matrix preservation between two
*visited distinct* parts gives BOTH side-coordinate transport laws
and the affine-compatible skeleton equation for their canonical
anchor multipliers. -/
theorem partialGaugeMultiplier_pair
    (s : AffineAntiInvolution G)
    (S : Set V) (p : S → V) (ι : Equiv.Perm I)
    (cls : V → I) (a : V → I → G) (K : I → I → G)
    (hcolour : ∀ x y : S, cls x.val ≠ cls y.val →
      gaugeColour s (a x.val (cls y.val))
        (K (cls x.val) (cls y.val)) (a y.val (cls x.val)) =
      gaugeColour s (a (p x) (ι (cls y.val)))
        (K (ι (cls x.val)) (ι (cls y.val)))
        (a (p y) (ι (cls x.val))))
    (i j : I)
    (hi : ∃ x : S, cls x.val = i)
    (hj : ∃ y : S, cls y.val = j)
    (hij : i ≠ j) :
    (∀ x : S, cls x.val = i →
      a (p x) (ι j) = partialGaugeMultiplier S p ι cls a i j * a x.val j) ∧
    (∀ y : S, cls y.val = j →
      a (p y) (ι i) = partialGaugeMultiplier S p ι cls a j i * a y.val i) ∧
    s.normalized (partialGaugeMultiplier S p ι cls a i j) *
      (K (ι i) (ι j))⁻¹ * partialGaugeMultiplier S p ι cls a j i =
      (K i j)⁻¹ := by
  classical
  let X : Type w := {x : S // cls x.val = i}
  let Y : Type w := {y : S // cls y.val = j}
  let x₀ : X := ⟨Classical.choose hi, Classical.choose_spec hi⟩
  let y₀ : Y := ⟨Classical.choose hj, Classical.choose_spec hj⟩
  let l : X → G := fun x => a x.val.val j
  let l' : X → G := fun x => a (p x.val) (ι j)
  let r : Y → G := fun y => a y.val.val i
  let r' : Y → G := fun y => a (p y.val) (ι i)
  have hmat : ∀ x : X, ∀ y : Y,
      gaugeColour s (l x) (K i j) (r y) =
        gaugeColour s (l' x) (K (ι i) (ι j)) (r' y) := by
    intro x y
    have hne : cls x.val.val ≠ cls y.val.val := by
      intro heq
      exact hij (x.property.symm.trans (heq.trans y.property))
    have hc := hcolour x.val y.val hne
    simpa only [x.property, y.property] using hc
  obtain ⟨hu, hv, hK⟩ :=
    anchored_partial_gauge_multipliers s l l' r r'
      (K i j) (K (ι i) (ι j)) hmat x₀ y₀
  have hmij := partialGaugeMultiplier_visited_ne S p ι cls a i j hi hij
  have hmji := partialGaugeMultiplier_visited_ne S p ι cls a j i hj hij.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have h := hu (⟨x, hx⟩ : X)
    change a (p x) (ι j) =
      (a (p (Classical.choose hi)) (ι j) *
        (a (Classical.choose hi).val j)⁻¹) * a x.val j at h
    calc
      a (p x) (ι j) =
          (a (p (Classical.choose hi)) (ι j) *
            (a (Classical.choose hi).val j)⁻¹) * a x.val j := h
      _ = partialGaugeMultiplier S p ι cls a i j * a x.val j := by
        rw [hmij]
  · intro y hy
    have h := hv (⟨y, hy⟩ : Y)
    change a (p y) (ι i) =
      (a (p (Classical.choose hj)) (ι i) *
        (a (Classical.choose hj).val i)⁻¹) * a y.val i at h
    calc
      a (p y) (ι i) =
          (a (p (Classical.choose hj)) (ι i) *
            (a (Classical.choose hj).val i)⁻¹) * a y.val i := h
      _ = partialGaugeMultiplier S p ι cls a j i * a y.val i := by
        rw [hmji]
  · rw [hmij, hmji]
    exact hK

/-- The multipliers form one coherent family simultaneously on
ALL visited old parts, including diagonal i=j where normalization
a(x,cls x)=1 is indispensable. The first output is (3.14), the
second is the full ordered affine compatibility law (3.15). -/
theorem partialGaugeMultiplier_properties
    (s : AffineAntiInvolution G)
    (S : Set V) (p : S → V) (ι : Equiv.Perm I)
    (cls : V → I) (a : V → I → G) (K : I → I → G)
    (hdiag : ∀ x : V, a x (cls x) = 1)
    (hpart : ∀ x : S, cls (p x) = ι (cls x.val))
    (hcolour : ∀ x y : S, cls x.val ≠ cls y.val →
      gaugeColour s (a x.val (cls y.val))
        (K (cls x.val) (cls y.val)) (a y.val (cls x.val)) =
      gaugeColour s (a (p x) (ι (cls y.val)))
        (K (ι (cls x.val)) (ι (cls y.val)))
        (a (p y) (ι (cls x.val)))) :
    (∀ (x : S) (j : I), (∃ y : S, cls y.val = j) →
      partialGaugeMultiplier S p ι cls a (cls x.val) j * a x.val j =
        a (p x) (ι j)) ∧
    (∀ (i j : I),
      (∃ x : S, cls x.val = i) →
      (∃ y : S, cls y.val = j) → i ≠ j →
        s.normalized (partialGaugeMultiplier S p ι cls a i j) *
          (K (ι i) (ι j))⁻¹ * partialGaugeMultiplier S p ι cls a j i =
            (K i j)⁻¹) := by
  classical
  constructor
  · intro x j hj
    by_cases heq : cls x.val = j
    · subst j
      rw [partialGaugeMultiplier_diag S p ι cls a (cls x.val),
        one_mul, hdiag x.val]
      have ht : a (p x) (ι (cls x.val)) = 1 := by
        rw [← hpart x]
        exact hdiag (p x)
      exact ht.symm
    · have hi : ∃ z : S, cls z.val = cls x.val := ⟨x, rfl⟩
      have h := (partialGaugeMultiplier_pair
        s S p ι cls a K hcolour (cls x.val) j hi hj heq).1 x rfl
      exact h.symm
  · intro i j hi hj hij
    exact (partialGaugeMultiplier_pair s S p ι cls a K
      hcolour i j hi hj hij).2.2

end SemigenericEPPA
