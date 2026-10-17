import SemigenericEPPA.Algebra.Rectangle

/-!
# The noncommutative one-point corner-amalgamation kernel

Let F : X × Y → G be a rectangle matrix. Suppose separately that
we add a new row r : Y → G and a new column c : X → G, each satisfying
all pre-existing rectangles. The missing cross-edge is *forced*:

  F(new row, new column) = r(q) * F(p,q)⁻¹ * c(p).

The completed matrix on Option X × Option Y is rank-one, hence
satisfies EVERY rectangle. The value is unique and independent of
the choice of old anchors p,q.

This is the essential nonabelian equation (2.4) in the one-point SAP
proof. It is not yet the full amalgamation theorem: part-equivalence
patterns, reversed raw colours and the lifting through φ remain to do.
-/

namespace SemigenericEPPA

universe u v w

variable {G : Type u} [Group G] {X : Type v} {Y : Type w}

/-- Put one new row and one new column around an existing matrix. -/
def extendCorner
    (F : X → Y → G) (r : Y → G) (c : X → G) (corner : G) :
    Option X → Option Y → G
  | some x, some y => F x y
  | none, some y => r y
  | some x, none => c x
  | none, none => corner

/-- The noncommutative missing-corner expression at two old anchors. -/
def forcedCorner (F : X → Y → G)
    (r : Y → G) (c : X → G) (p : X) (q : Y) : G :=
  r q * (F p q)⁻¹ * c p

/-- The new row satisfies the rectangles involving only old columns. -/
def RowCompatible (F : X → Y → G)
    (r : Y → G) (p : X) (q : Y) : Prop :=
  ∀ y, (r q)⁻¹ * r y = (F p q)⁻¹ * F p y

/-- The new column satisfies the rectangles involving only old rows. -/
def ColumnCompatible (F : X → Y → G)
    (c : X → G) (p : X) (q : Y) : Prop :=
  ∀ x, (F x q)⁻¹ * c x = (F p q)⁻¹ * c p

theorem rowCompatible_formula
    (F : X → Y → G) (r : Y → G) (p : X) (q : Y)
    (hr : RowCompatible F r p q) (y : Y) :
    r y = r q * ((F p q)⁻¹ * F p y) := by
  calc
    r y = r q * ((r q)⁻¹ * r y) := by simp [mul_assoc]
    _ = r q * ((F p q)⁻¹ * F p y) := by rw [hr y]

theorem columnCompatible_formula
    (F : X → Y → G) (c : X → G) (p : X) (q : Y)
    (hc : ColumnCompatible F c p q) (x : X) :
    c x = F x q * ((F p q)⁻¹ * c p) := by
  calc
    c x = F x q * ((F x q)⁻¹ * c x) := by simp [mul_assoc]
    _ = F x q * ((F p q)⁻¹ * c p) := by rw [hc x]

/-- The completed matrix is genuinely rank-one, not merely a local
corner identity. This handles all sixteen positions of a rectangle
in one factorization proof. -/
theorem forcedCorner_rankOne
    (F : X → Y → G) (hF : RectangleLaw F)
    (r : Y → G) (c : X → G) (p : X) (q : Y)
    (hr : RowCompatible F r p q)
    (hc : ColumnCompatible F c p q) :
    IsRankOne (extendCorner F r c (forcedCorner F r c p q)) := by
  refine ⟨(fun x => match x with
      | some a => F a q
      | none => r q),
    (fun y => match y with
      | some b => (F p q)⁻¹ * F p b
      | none => (F p q)⁻¹ * c p), ?_⟩
  intro x y
  cases x with
  | none =>
    cases y with
    | none =>
      change r q * (F p q)⁻¹ * c p =
        r q * ((F p q)⁻¹ * c p)
      exact mul_assoc _ _ _
    | some b =>
      change r b = r q * ((F p q)⁻¹ * F p b)
      exact rowCompatible_formula F r p q hr b
  | some a =>
    cases y with
    | none =>
      change c a = F a q * ((F p q)⁻¹ * c p)
      exact columnCompatible_formula F c p q hc a
    | some b =>
      change F a b = F a q * ((F p q)⁻¹ * F p b)
      simpa only [mul_assoc] using factor_of_rectangle F hF p q a b

/-- All rectangles, including those through the new corner, are
satisfied by the unique forced completion. -/
theorem forcedCorner_rectangle
    (F : X → Y → G) (hF : RectangleLaw F)
    (r : Y → G) (c : X → G) (p : X) (q : Y)
    (hr : RowCompatible F r p q)
    (hc : ColumnCompatible F c p q) :
    RectangleLaw (extendCorner F r c (forcedCorner F r c p q)) :=
  rectangle_of_rankOne _ (forcedCorner_rankOne F hF r c p q hr hc)

/-- Any completion satisfying all rectangles must use the forced
corner value. This does not assume row/column compatibility separately. -/
theorem corner_unique
    (F : X → Y → G) (r : Y → G) (c : X → G)
    (p : X) (q : Y) (corner : G)
    (h : RectangleLaw (extendCorner F r c corner)) :
    corner = forcedCorner F r c p q := by
  have hf := factor_of_rectangle (extendCorner F r c corner)
    h (some p) (some q) none none
  simpa only [extendCorner, forcedCorner] using hf

/-- The corner formula computed at any two anchors is independent
of their choice, provided the common old matrix and the new row/column
are individually compatible. -/
theorem forcedCorner_anchor_independent
    (F : X → Y → G) (hF : RectangleLaw F)
    (r : Y → G) (c : X → G) (p a : X) (q b : Y)
    (hr : RowCompatible F r p q)
    (hc : ColumnCompatible F c p q) :
    forcedCorner F r c p q = forcedCorner F r c a b := by
  have hcompleted := forcedCorner_rectangle F hF r c p q hr hc
  exact (corner_unique F r c a b (forcedCorner F r c p q)
    hcompleted)

end SemigenericEPPA
