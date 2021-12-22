/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebra.algebra.basic
import algebraic_geometry.elliptic_curve.EllipticCurve

/-!
# The group of rational points on an elliptic curve over a field
-/

open_locale classical
noncomputable theory

namespace EllipticCurve

variables {K : Type*} [field K]
variables (E : EllipticCurve K)
variables (L : Type*) [field L] [algebra K L]

notation K↑L := algebra_map K L

/-- The group of `L`-rational points `E(L)` on an elliptic curve `E` over `K`,
    consisting of the point at infinity and the affine points satisfying a Weierstrass equation. -/
inductive point
  | zero
  | some (x y : L) (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
                      = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6)

notation E{L} := point E L

open point

----------------------------------------------------------------------------------------------------
/-!
## Zero in `E(L)`
-/
----------------------------------------------------------------------------------------------------

/-- Zero in `E(L)`. -/
def zero : E{L} := zero

/-- `E(L)` has zero. -/
instance point.has_zero : has_zero (E{L}) := ⟨zero E L⟩

/-- `E(L)` is inhabited. -/
instance point.inhabited : inhabited (E{L}) := ⟨zero E L⟩

----------------------------------------------------------------------------------------------------
/-!
## Negation in `E(L)`
-/
----------------------------------------------------------------------------------------------------

/-- Negation of an affine point in `E(L)` is in `E(L)`. -/
lemma neg_some.weierstrass
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
               = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6) :
  (-y - (K↑L)E.a1 * x - (K↑L)E.a3) ^ 2 + (K↑L)E.a1 * x * (-y - (K↑L)E.a1 * x - (K↑L)E.a3)
    + (K↑L)E.a3 * (-y - (K↑L)E.a1 * x - (K↑L)E.a3)
    = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6 :=
by rw [← w]; ring

/-- Negate an affine point in `E(L)`. -/
def neg_some.def
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
               = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6) : E{L} :=
some x (-y - (K↑L)E.a1 * x - (K↑L)E.a3) $ neg_some.weierstrass E L w

/-- Negation in `E(L)`. -/
def neg : E{L} → E{L}
  | 0            := 0
  | (some _ _ w) := neg_some.def E L w

/-- `E(L)` has negation. -/
instance point.has_neg : has_neg (E{L}) := ⟨neg E L⟩

/-- Negation of zero in `E(L)` is zero. -/
@[simp]
lemma neg_zero : -(0 : E{L}) = 0 := rfl

/-- Negation of an affine point in `E(L)` is an affine point. -/
@[simp]
lemma neg_some
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
               = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6) :
  -some x y w = some x (-y - (K↑L)E.a1 * x - (K↑L)E.a3) (neg_some.weierstrass E L w) :=
rfl

----------------------------------------------------------------------------------------------------
/-!
## Doubling in `E(L)`
-/
----------------------------------------------------------------------------------------------------

/-- Doubling of an affine point in `E(L)` is in `E(L)`. -/
lemma dbl_some.weierstrass
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
                  = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6)
  (y_ne : 2 * y + (K↑L)E.a1 * x + (K↑L)E.a3 ≠ 0)
  {l x' y' : L} (l_def : l  = (3 * x ^ 2 + 2 * (K↑L)E.a2 * x + (K↑L)E.a4 - (K↑L)E.a1 * y)
                              * (2 * y + (K↑L)E.a1 * x + (K↑L)E.a3)⁻¹)
                (x_def : x' = l ^ 2 + (K↑L)E.a1 * l - (K↑L)E.a2 - 2 * x)
                (y_def : y' = -l * x' - (K↑L)E.a1 * x' - y + l * x - (K↑L)E.a3) :
  y' ^ 2 + (K↑L)E.a1 * x' * y' + (K↑L)E.a3 * y'
    = x' ^ 3 + (K↑L)E.a2 * x' ^ 2 + (K↑L)E.a4 * x' + (K↑L)E.a6 :=
begin
  -- rewrite Weierstrass equation as w(x, y) = 0
  rw [← sub_eq_zero] at w,
  -- rewrite y
  have y_rw :
    y' ^ 2 + (K↑L)E.a1 * x' * y' + (K↑L)E.a3 * y'
      = x' ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
      + x' * (-2 * x * l ^ 2 - (K↑L)E.a1 * x * l + 2 * y * l + (K↑L)E.a3 * l + (K↑L)E.a1 * y)
      + (x ^ 2 * l ^ 2 - 2 * x * y * l - (K↑L)E.a3 * x * l + y ^ 2 + (K↑L)E.a3 * y) :=
  by rw [y_def]; ring,
  -- rewrite x
  have x_rw :
    x' ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
      + x' * (-2 * x * l ^ 2 - (K↑L)E.a1 * x * l + 2 * y * l + (K↑L)E.a3 * l + (K↑L)E.a1 * y)
      + (x ^ 2 * l ^ 2 - 2 * x * y * l - (K↑L)E.a3 * x * l + y ^ 2 + (K↑L)E.a3 * y)
      - (x' ^ 3 + (K↑L)E.a2 * x' ^ 2 + (K↑L)E.a4 * x' + (K↑L)E.a6)
      = l * (l * (l * (2 * y + (K↑L)E.a1 * x + (K↑L)E.a3)
                  + (-3 * x ^ 2 + (K↑L)E.a1 ^ 2 * x - 2 * (K↑L)E.a2 * x + 3 * (K↑L)E.a1 * y
                     + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4))
             + (-6 * (K↑L)E.a1 * x ^ 2 - 6 * x * y - 3 * (K↑L)E.a1 * (K↑L)E.a2 * x
                - 3 * (K↑L)E.a3 * x + (K↑L)E.a1 ^ 2 * y - 2 * (K↑L)E.a2 * y - (K↑L)E.a1 * (K↑L)E.a4
                - (K↑L)E.a2 * (K↑L)E.a3))
        + (8 * x ^ 3 + 8 * (K↑L)E.a2 * x ^ 2 - 2 * (K↑L)E.a1 * x * y + y ^ 2 + 2 * (K↑L)E.a2 ^ 2 * x
           + 2 * (K↑L)E.a4 * x - (K↑L)E.a1 * (K↑L)E.a2 * y + (K↑L)E.a3 * y + (K↑L)E.a2 * (K↑L)E.a4
           - (K↑L)E.a6) :=
  by rw [x_def]; ring,
  -- rewrite l step 1
  have l_rw_1 :
    l * (2 * y + (K↑L)E.a1 * x + (K↑L)E.a3)
      + (-3 * x ^ 2 + (K↑L)E.a1 ^ 2 * x - 2 * (K↑L)E.a2 * x + 3 * (K↑L)E.a1 * y
         + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4)
      = (2 * y + (K↑L)E.a1 * x + (K↑L)E.a3) * (K↑L)E.a1 :=
  by rw [l_def, inv_mul_cancel_right₀ y_ne]; ring,
  -- rewrite l step 2
  have l_rw_2 :
    l * ((2 * y + (K↑L)E.a1 * x + (K↑L)E.a3) * (K↑L)E.a1)
      + (-6 * (K↑L)E.a1 * x ^ 2 - 6 * x * y - 3 * (K↑L)E.a1 * (K↑L)E.a2 * x - 3 * (K↑L)E.a3 * x
         + (K↑L)E.a1 ^ 2 * y - 2 * (K↑L)E.a2 * y - (K↑L)E.a1 * (K↑L)E.a4 - (K↑L)E.a2 * (K↑L)E.a3)
      = (2 * y + (K↑L)E.a1 * x + (K↑L)E.a3) * (-3 * x - (K↑L)E.a2) :=
  by rw [← mul_assoc l, l_def, inv_mul_cancel_right₀ y_ne]; ring,
  -- rewrite l step 3
  have l_rw_3 :
    l * ((2 * y + (K↑L)E.a1 * x + (K↑L)E.a3) * (-3 * x - (K↑L)E.a2))
      + (8 * x ^ 3 + 8 * (K↑L)E.a2 * x ^ 2 - 2 * (K↑L)E.a1 * x * y + y ^ 2 + 2 * (K↑L)E.a2 ^ 2 * x
         + 2 * (K↑L)E.a4 * x - (K↑L)E.a1 * (K↑L)E.a2 * y + (K↑L)E.a3 * y + (K↑L)E.a2 * (K↑L)E.a4
         - (K↑L)E.a6)
      = 0 :=
  by rw [← mul_assoc l, l_def, inv_mul_cancel_right₀ y_ne, ← w]; ring,
  -- rewrite Weierstrass equation as w'(x', y') = 0 and sequence steps
  rw [← sub_eq_zero, y_rw, x_rw, l_rw_1, l_rw_2, l_rw_3]
end

/-- Double an affine point `(x, y) ∈ E(L)` with `2y + a₁x + a₃ ≠ 0`. -/
def dbl_some.def
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
               = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6)
  (y_ne : 2 * y + (K↑L)E.a1 * x + (K↑L)E.a3 ≠ 0) : E{L} :=
let l  := (3 * x ^ 2 + 2 * (K↑L)E.a2 * x + (K↑L)E.a4 - (K↑L)E.a1 * y)
          * (2 * y + (K↑L)E.a1 * x + (K↑L)E.a3)⁻¹,
    x' := l ^ 2 + (K↑L)E.a1 * l - (K↑L)E.a2 - 2 * x,
    y' := -l * x' - (K↑L)E.a1 * x' - y + l * x - (K↑L)E.a3
in  some x' y' $ dbl_some.weierstrass E L w y_ne rfl rfl rfl

/-- Doubling in `E(L)`. -/
def dbl : E{L} → E{L}
  | 0            := 0
  | (some x y w) :=
    if y_ne : 2 * y + (K↑L)E.a1 * x + (K↑L)E.a3 ≠ 0 then dbl_some.def E L w y_ne else 0

/-- Doubling of zero in `E(L)` is zero. -/
@[simp]
lemma dbl_zero : dbl E L 0 = 0 := rfl

/-- Doubling of an affine point `(x, y) ∈ E(L)` with `2y + a₁x + a₃ ≠ 0` is an affine point. -/
lemma dbl_some
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
               = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6)
  (y_ne : 2 * y + (K↑L)E.a1 * x + (K↑L)E.a3 ≠ 0) :
  dbl E L (some x y w) = dbl_some.def E L w y_ne :=
by unfold dbl; rw [dif_pos y_ne]

/-- Doubling of an affine point `(x, y) ∈ E(L)` with `2y + a₁x + a₃ = 0` is zero. -/
@[simp]
lemma dbl_some'
  {x y : L} (w : y ^ 2 + (K↑L)E.a1 * x * y + (K↑L)E.a3 * y
               = x ^ 3 + (K↑L)E.a2 * x ^ 2 + (K↑L)E.a4 * x + (K↑L)E.a6)
  (y_eq : 2 * y + (K↑L)E.a1 * x + (K↑L)E.a3 = 0) :
  dbl E L (some x y w) = 0 :=
by unfold dbl; rw [dif_neg (by rw [not_not]; exact y_eq)]

----------------------------------------------------------------------------------------------------
/-!
## Addition in `E(L)`
-/
----------------------------------------------------------------------------------------------------

/-- Addition of affine points in `E(L)` is in `E(L)`. -/
lemma add_some_some.weierstrass
  {x₁ y₁ : L} (w₁ : y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                  = x₁ ^ 3 + (K↑L)E.a2 * x₁ ^ 2 + (K↑L)E.a4 * x₁ + (K↑L)E.a6)
  {x₂ y₂ : L} (w₂ : y₂ ^ 2 + (K↑L)E.a1 * x₂ * y₂ + (K↑L)E.a3 * y₂
                  = x₂ ^ 3 + (K↑L)E.a2 * x₂ ^ 2 + (K↑L)E.a4 * x₂ + (K↑L)E.a6)
  (x_ne : x₁ - x₂ ≠ 0)
  {l x₃ y₃ : L} (l_def : l  = (y₁ - y₂) * (x₁ - x₂)⁻¹)
                (x_def : x₃ = l ^ 2 + (K↑L)E.a1 * l - (K↑L)E.a2 - x₁ - x₂)
                (y_def : y₃ = -l * x₃ - (K↑L)E.a1 * x₃ - y₁ + l * x₁ - (K↑L)E.a3) :
  y₃ ^ 2 + (K↑L)E.a1 * x₃ * y₃ + (K↑L)E.a3 * y₃
    = x₃ ^ 3 + (K↑L)E.a2 * x₃ ^ 2 + (K↑L)E.a4 * x₃ + (K↑L)E.a6 :=
begin
  -- rewrite Weierstrass equations as w₁(x₁, y₁) = 0 and w₂(x₂, y₂) = 0
  rw [← sub_eq_zero] at w₁ w₂,
  -- rewrite y
  have y_rw :
    y₃ ^ 2 + (K↑L)E.a1 * x₃ * y₃ + (K↑L)E.a3 * y₃
      = x₃ ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
      + x₃ * (-2 * x₁ * l ^ 2 - (K↑L)E.a1 * x₁ * l + 2 * y₁ * l + (K↑L)E.a3 * l + (K↑L)E.a1 * y₁)
      + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (K↑L)E.a3 * x₁ * l + y₁ ^ 2 + (K↑L)E.a3 * y₁) :=
  by rw [y_def]; ring,
  -- rewrite x
  have x_rw :
    x₃ ^ 2 * (l ^ 2 + (K↑L)E.a1 * l)
      + x₃ * (-2 * x₁ * l ^ 2 - (K↑L)E.a1 * x₁ * l + 2 * y₁ * l + (K↑L)E.a3 * l + (K↑L)E.a1 * y₁)
      + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (K↑L)E.a3 * x₁ * l + y₁ ^ 2 + (K↑L)E.a3 * y₁)
      - (x₃ ^ 3 + (K↑L)E.a2 * x₃ ^ 2 + (K↑L)E.a4 * x₃ + (K↑L)E.a6)
      = l * (l * (l * (l * (x₁ - x₂) * (-1)
                       + (-(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3))
                  + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (K↑L)E.a1 ^ 2 * x₂ - 2 * (K↑L)E.a2 * x₂
                     + 3 * (K↑L)E.a1 * y₁ + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4))
             + (-(K↑L)E.a1 * x₁ ^ 2 - 3 * (K↑L)E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (K↑L)E.a1 * x₂ ^ 2
                - 2 * x₂ * y₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₁ - 2 * (K↑L)E.a3 * x₁
                - 2 * (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂ + (K↑L)E.a1 ^ 2 * y₁
                - 2 * (K↑L)E.a2 * y₁ - (K↑L)E.a1 * (K↑L)E.a4 - (K↑L)E.a2 * (K↑L)E.a3))
        + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (K↑L)E.a2 * x₁ ^ 2
           + 4 * (K↑L)E.a2 * x₁ * x₂ - (K↑L)E.a1 * x₁ * y₁ + 2 * (K↑L)E.a2 * x₂ ^ 2
           - (K↑L)E.a1 * x₂ * y₁ + y₁ ^ 2 + (K↑L)E.a2 ^ 2 * x₁ + (K↑L)E.a4 * x₁ + (K↑L)E.a2 ^ 2 * x₂
           + (K↑L)E.a4 * x₂ - (K↑L)E.a1 * (K↑L)E.a2 * y₁ + (K↑L)E.a3 * y₁ + (K↑L)E.a2 * (K↑L)E.a4
           - (K↑L)E.a6) :=
  by rw [x_def]; ring,
  -- rewrite l auxiliary tactic
  have l_rw :
    ∀ (a b c : L), l * a + b = c ↔ (y₁ - y₂) * a + (x₁ - x₂) * b + 0 = (x₁ - x₂) * c + 0 :=
  by intros a b c; rw [← mul_right_inj' x_ne, mul_add (x₁ - x₂), ← mul_assoc (x₁ - x₂) l];
     rw [mul_comm (x₁ - x₂) l, l_def, inv_mul_cancel_right₀ x_ne, ← add_left_inj (0 : L)],
  -- rewrite l step 1
  have l_rw_1 :
    l * (x₁ - x₂) * (-1) + (-(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3)
      = -(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3 - y₁ + y₂ :=
  by rw [l_def, inv_mul_cancel_right₀ x_ne]; ring,
  -- rewrite l step 2
  have l_rw_2 :
    l * (-(K↑L)E.a1 * x₁ + 2 * (K↑L)E.a1 * x₂ + 2 * y₁ + (K↑L)E.a3 - y₁ + y₂)
      + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (K↑L)E.a1 ^ 2 * x₂ - 2 * (K↑L)E.a2 * x₂
         + 3 * (K↑L)E.a1 * y₁ + (K↑L)E.a1 * (K↑L)E.a3 - (K↑L)E.a4)
      = 2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (K↑L)E.a2 * x₁ + (K↑L)E.a1 ^ 2 * x₂ + (K↑L)E.a2 * x₂
      - 2 * (K↑L)E.a2 * x₂ + (K↑L)E.a1 * y₁ + (K↑L)E.a1 * y₂ + (K↑L)E.a1 * (K↑L)E.a3 :=
  by rw [l_rw]; nth_rewrite_rhs 0 [← w₁]; nth_rewrite_lhs 0 [← w₂]; ring,
  -- rewrite l step 3
  have l_rw_3 :
    l * (2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (K↑L)E.a2 * x₁ + (K↑L)E.a1 ^ 2 * x₂ + (K↑L)E.a2 * x₂
         - 2 * (K↑L)E.a2 * x₂ + (K↑L)E.a1 * y₁ + (K↑L)E.a1 * y₂ + (K↑L)E.a1 * (K↑L)E.a3)
      + (-(K↑L)E.a1 * x₁ ^ 2 - 3 * (K↑L)E.a1 * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (K↑L)E.a1 * x₂ ^ 2
         - 2 * x₂ * y₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₁ - 2 * (K↑L)E.a3 * x₁
         - 2 * (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂ + (K↑L)E.a1 ^ 2 * y₁ - 2 * (K↑L)E.a2 * y₁
         - (K↑L)E.a1 * (K↑L)E.a4 - (K↑L)E.a2 * (K↑L)E.a3)
      = -2 * (K↑L)E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (K↑L)E.a1 * x₂ ^ 2 - x₂ * y₁
        - x₂ * y₂ - 2 * (K↑L)E.a3 * x₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂
        - (K↑L)E.a2 * y₁ - (K↑L)E.a2 * y₂ - (K↑L)E.a2 * (K↑L)E.a3 :=
  by apply_fun (λ x, x * (K↑L)E.a1) at w₁ w₂; rw [zero_mul] at w₁ w₂; rw [l_rw];
     nth_rewrite_rhs 0 [← w₁]; nth_rewrite_lhs 0 [← w₂]; ring,
  -- rewrite l step 4
  have l_rw_4 :
    l * (-2 * (K↑L)E.a1 * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (K↑L)E.a1 * x₂ ^ 2 - x₂ * y₁
         - x₂ * y₂ - 2 * (K↑L)E.a3 * x₁ - (K↑L)E.a1 * (K↑L)E.a2 * x₂ - (K↑L)E.a3 * x₂
         - (K↑L)E.a2 * y₁ - (K↑L)E.a2 * y₂ - (K↑L)E.a2 * (K↑L)E.a3)
      + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (K↑L)E.a2 * x₁ ^ 2
         + 4 * (K↑L)E.a2 * x₁ * x₂ - (K↑L)E.a1 * x₁ * y₁ + 2 * (K↑L)E.a2 * x₂ ^ 2
         - (K↑L)E.a1 * x₂ * y₁ + y₁ ^ 2 + (K↑L)E.a2 ^ 2 * x₁ + (K↑L)E.a4 * x₁ + (K↑L)E.a2 ^ 2 * x₂
         + (K↑L)E.a4 * x₂ - (K↑L)E.a1 * (K↑L)E.a2 * y₁ + (K↑L)E.a3 * y₁ + (K↑L)E.a2 * (K↑L)E.a4
         - (K↑L)E.a6)
      = 0 :=
  by apply_fun (λ x, x * (x₁ + 2 * x₂ + (K↑L)E.a2)) at w₁;
     apply_fun (λ x, x * (2 * x₁ + x₂ + (K↑L)E.a2)) at w₂;
     rw [zero_mul] at w₁ w₂; rw [l_rw];
     nth_rewrite_lhs 0 [← w₁]; nth_rewrite_rhs 1 [← w₂]; ring,
  -- rewrite Weierstrass equation as w₃(x₃, y₃) = 0 and sequence steps
  rw [← sub_eq_zero, y_rw, x_rw, l_rw_1, l_rw_2, l_rw_3, l_rw_4]
end

/-- Add affine points in `E(L)`. -/
def add_some_some.def
  {x₁ y₁ : L} (w₁ : y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                  = x₁ ^ 3 + (K↑L)E.a2 * x₁ ^ 2 + (K↑L)E.a4 * x₁ + (K↑L)E.a6)
  {x₂ y₂ : L} (w₂ : y₂ ^ 2 + (K↑L)E.a1 * x₂ * y₂ + (K↑L)E.a3 * y₂
                  = x₂ ^ 3 + (K↑L)E.a2 * x₂ ^ 2 + (K↑L)E.a4 * x₂ + (K↑L)E.a6)
  (x_ne : x₁ - x₂ ≠ 0) : E{L} :=
let l  := (y₁ - y₂) * (x₁ - x₂)⁻¹,
    x₃ := l ^ 2 + (K↑L)E.a1 * l - (K↑L)E.a2 - x₁ - x₂,
    y₃ := -l * x₃ - (K↑L)E.a1 * x₃ - y₁ + l * x₁ - (K↑L)E.a3
in  some x₃ y₃ $ add_some_some.weierstrass E L w₁ w₂ x_ne rfl rfl rfl

/-- For all affine points `(x₁, y₁), (x₂, y₂) ∈ E(L)`,
    if `x₁ = x₂` and `y₁ + y₂ + a₁x₂ + a₃ ≠ 0` then `y₁ = y₂`. -/
private lemma add_some_some_rw
  {x₁ y₁ : L} (w₁ : y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                  = x₁ ^ 3 + (K↑L)E.a2 * x₁ ^ 2 + (K↑L)E.a4 * x₁ + (K↑L)E.a6)
  {x₂ y₂ : L} (w₂ : y₂ ^ 2 + (K↑L)E.a1 * x₂ * y₂ + (K↑L)E.a3 * y₂
                  = x₂ ^ 3 + (K↑L)E.a2 * x₂ ^ 2 + (K↑L)E.a4 * x₂ + (K↑L)E.a6)
  (x_eq : x₁ - x₂ = 0) (y_ne : y₁ + y₂ + (K↑L)E.a1 * x₂ + (K↑L)E.a3 ≠ 0) :
  2 * y₁ + (K↑L)E.a1 * x₁ + (K↑L)E.a3 ≠ 0 :=
begin
  rw [sub_eq_zero] at x_eq,
  subst x_eq,
  have y_rw :
    y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁ - (y₂ ^ 2 + (K↑L)E.a1 * x₁ * y₂ + (K↑L)E.a3 * y₂)
      = (y₁ - y₂) * (y₁ + y₂ + (K↑L)E.a1 * x₁ + (K↑L)E.a3) :=
  by ring,
  rw [← w₂, ← sub_eq_zero, y_rw, mul_eq_zero, sub_eq_zero] at w₁,
  cases w₁,
  { subst w₁,
    rw [two_mul],
    exact y_ne },
  { contradiction },
end

/-- Addition in `E(L)`. -/
def add : E{L} → E{L} → E{L}
  | 0               P               := P
  | P               0               := P
  | (some x₁ y₁ w₁) (some x₂ y₂ w₂) :=
    if x_ne : x₁ - x₂ ≠ 0 then add_some_some.def E L w₁ w₂ x_ne
    else if y_ne : y₁ + y₂ + (K↑L)E.a1 * x₂ + (K↑L)E.a3 ≠ 0 then dbl_some.def E L w₁ $
      add_some_some_rw E L w₁ w₂ (by rw [not_not] at x_ne; exact x_ne) y_ne else 0

/-- `E(L)` has addition. -/
instance point.has_add : has_add (E{L}) := ⟨add E L⟩

/-- Addition of zero and `P ∈ E(L)` is `P`. -/
@[simp]
lemma zero_add : ∀ P : E{L}, 0 + P = P := λ P, by cases P; refl

/-- Addition of `P ∈ E(L)` and zero is `P`. -/
@[simp]
lemma add_zero : ∀ P : E{L}, P + 0 = P := λ P, by cases P; refl

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(L)` with `x₁ - x₂ ≠ 0` is an affine point. -/
lemma add_some_some
  {x₁ y₁ : L} (w₁ : y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                  = x₁ ^ 3 + (K↑L)E.a2 * x₁ ^ 2 + (K↑L)E.a4 * x₁ + (K↑L)E.a6)
  {x₂ y₂ : L} (w₂ : y₂ ^ 2 + (K↑L)E.a1 * x₂ * y₂ + (K↑L)E.a3 * y₂
                  = x₂ ^ 3 + (K↑L)E.a2 * x₂ ^ 2 + (K↑L)E.a4 * x₂ + (K↑L)E.a6)
  (x_ne : x₁ - x₂ ≠ 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂ = add_some_some.def E L w₁ w₂ x_ne :=
by unfold has_add.add add; rw [dif_pos x_ne]

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(L)` with `x₁ - x₂ = 0`
    and `y₁ + y₂ + a₁x₂ + a₃ ≠ 0` is doubling of `(x₁, y₁)`. -/
lemma add_some_some'
  {x₁ y₁ : L} (w₁ : y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                  = x₁ ^ 3 + (K↑L)E.a2 * x₁ ^ 2 + (K↑L)E.a4 * x₁ + (K↑L)E.a6)
  {x₂ y₂ : L} (w₂ : y₂ ^ 2 + (K↑L)E.a1 * x₂ * y₂ + (K↑L)E.a3 * y₂
                  = x₂ ^ 3 + (K↑L)E.a2 * x₂ ^ 2 + (K↑L)E.a4 * x₂ + (K↑L)E.a6)
  (x_eq : x₁ - x₂ = 0) (y_ne : y₁ + y₂ + (K↑L)E.a1 * x₂ + (K↑L)E.a3 ≠ 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂ = dbl_some.def E L w₁ (add_some_some_rw E L w₁ w₂ x_eq y_ne) :=
by unfold has_add.add add; rw [dif_neg (by rw [not_not]; exact x_eq)]; rw [dif_pos y_ne]

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(L)` with `x₁ - x₂ = 0`
    and `y₁ + y₂ + a₁x₂ + a₃ = 0` is zero. -/
@[simp]
lemma add_some_some''
  {x₁ y₁ : L} (w₁ : y₁ ^ 2 + (K↑L)E.a1 * x₁ * y₁ + (K↑L)E.a3 * y₁
                  = x₁ ^ 3 + (K↑L)E.a2 * x₁ ^ 2 + (K↑L)E.a4 * x₁ + (K↑L)E.a6)
  {x₂ y₂ : L} (w₂ : y₂ ^ 2 + (K↑L)E.a1 * x₂ * y₂ + (K↑L)E.a3 * y₂
                  = x₂ ^ 3 + (K↑L)E.a2 * x₂ ^ 2 + (K↑L)E.a4 * x₂ + (K↑L)E.a6)
  (x_eq : x₁ - x₂ = 0) (y_eq : y₁ + y₂ + (K↑L)E.a1 * x₂ + (K↑L)E.a3 = 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂ = 0 :=
by unfold has_add.add add; rw [dif_neg (by rw [not_not]; exact x_eq)];
                           rw [dif_neg (by rw [not_not]; exact y_eq)]

----------------------------------------------------------------------------------------------------
/-!
## Axioms in `E(L)`
-/
----------------------------------------------------------------------------------------------------

/-- Left negation in `E(L)`. -/
@[simp]
lemma add_left_neg : ∀ P : E{L}, -P + P = 0
  | 0            := rfl
  | (some _ _ _) := by rw [neg_some, add_some_some'']; ring

/-- Commutativity in `E(L)`. -/
lemma add_comm : ∀ (P Q : E{L}), P + Q = Q + P
  | 0 _ := by simp
  | _ 0 := by simp
  | _ _ := sorry

/-- Associativity in `E(L)`. -/
lemma add_assoc : ∀ P Q R : E{L}, (P + Q) + R = P + (Q + R)
  | 0 _ _ := by simp
  | _ 0 _ := by simp
  | _ _ 0 := by simp
  | _ _ _ := sorry

/-- `E(L)` is an additive commutative group. -/
instance point.add_comm_group : add_comm_group (E{L}) :=
  { zero         := zero E L,
    neg          := neg E L,
    add          := add E L,
    zero_add     := zero_add E L,
    add_zero     := add_zero E L,
    add_left_neg := add_left_neg E L,
    add_comm     := add_comm E L,
    add_assoc    := add_assoc E L }

end EllipticCurve
