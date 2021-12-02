/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import analysis.normed_space.basic
import algebra.lattice_ordered_group
import topology.order.lattice

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

local notation `|`a`|` := abs a

/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `∥a∥ ≤ ∥b∥`. Then `α` is
said to be a normed lattice ordered group.
-/
class normed_lattice_add_comm_group (α : Type*)
  extends normed_group α, lattice α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(solid : ∀ a b : α, |a| ≤ |b| → ∥a∥ ≤ ∥b∥)

lemma solid {α : Type*} [normed_lattice_add_comm_group α] {a b : α} (h : |a| ≤ |b|) : ∥a∥ ≤ ∥b∥ :=
normed_lattice_add_comm_group.solid a b h

noncomputable
instance real.normed_lattice_add_comm_group : normed_lattice_add_comm_group ℝ :=
{ add_le_add_left := λ a b h c, add_le_add_left h c,
  solid := λ a b h, by { simp_rw real.norm_eq_abs, exact h} }

/--
A normed lattice ordered group is an ordered additive commutative group
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_to_ordered_add_comm_group {α : Type*}
  [h : normed_lattice_add_comm_group α] : ordered_add_comm_group α := { ..h }

/--
Let `α` be a normed group with a partial order. Then the order dual is also a normed group.
-/
@[priority 100] -- see Note [lower instance priority]
instance {α : Type*} : Π [normed_group α], normed_group (order_dual α) := id

/--
Let `α` be a normed lattice ordered group and let `a` and `b` be elements of `α`. Then `a⊓-a ≥ b⊓-b`
implies `∥a∥ ≤ ∥b∥`.
-/
lemma dual_solid {α : Type*} [normed_lattice_add_comm_group α] (a b : α) (h: b⊓-b ≤ a⊓-a) :
  ∥a∥ ≤ ∥b∥ :=
begin
  apply solid,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg a,
  rw ← neg_inf_eq_sup_neg,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg b,
  rw ← neg_inf_eq_sup_neg,
  finish,
end

/--
Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
@[priority 100] -- see Note [lower instance priority]
instance {α : Type*} [h: normed_lattice_add_comm_group α] :
  normed_lattice_add_comm_group (order_dual α) :=
{ add_le_add_left := begin
  intros a b h₁ c,
  rw ← order_dual.dual_le,
  rw ← order_dual.dual_le at h₁,
  apply h.add_le_add_left,
  exact h₁,
end,
solid := begin
  intros a b h₂,
  apply dual_solid,
  rw ← order_dual.dual_le at h₂,
  finish,
end, }

/--
Let `α` be a normed lattice ordered group, let `a` be an element of `α` and let `|a|` be the
absolute value of `a`. Then `∥|a|∥ = ∥a∥`.
-/
lemma norm_abs_eq_norm {α : Type*} [normed_lattice_add_comm_group α] (a : α) : ∥|a|∥ = ∥a∥ :=
le_antisymm (solid (le_of_eq (lattice_ordered_comm_group.abs_idempotent a).symm))
  (solid (le_of_eq (lattice_ordered_comm_group.abs_idempotent a)))

lemma norm_inf_sub_inf_le_add_norm {α : Type*} [normed_lattice_add_comm_group α] (a b c d : α) :
  ∥a ⊓ b - c ⊓ d∥ ≤ ∥a - c∥ + ∥b - d∥ :=
begin
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)],
  refine le_trans (solid _) (norm_add_le (|a - c|) (|b - d|)),
  rw lattice_ordered_comm_group.abs_pos_eq (|a - c| + |b - d|)
    (add_nonneg (lattice_ordered_comm_group.abs_pos (a - c))
      (lattice_ordered_comm_group.abs_pos (b - d))),
  calc |a ⊓ b - c ⊓ d| =
    |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| : by { rw sub_add_sub_cancel, }
  ... ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| : lattice_ordered_comm_group.abs_triangle _ _
  ... ≤ |a -c| + |b - d| : by
    { apply add_le_add,
      { exact lattice_ordered_comm_group.abs_inf_sub_inf_le_abs _ _ _, },
      { rw [@inf_comm _ _ c, @inf_comm _ _ c],
        exact lattice_ordered_comm_group.abs_inf_sub_inf_le_abs _ _ _, } },
end

/--
Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_has_continuous_inf {α : Type*}
  [normed_lattice_add_comm_group α] : has_continuous_inf α :=
⟨ continuous_iff_continuous_at.2 $ λ q, tendsto_iff_norm_tendsto_zero.2 $
begin
  have : ∀ p : α × α, ∥p.1 ⊓ p.2 - q.1 ⊓ q.2∥ ≤ ∥p.1 - q.1∥ + ∥p.2 - q.2∥,
    from λ _, norm_inf_sub_inf_le_add_norm _ _ _ _,
  refine squeeze_zero (λ e, norm_nonneg _) this _,
  convert (((continuous_fst.tendsto q).sub tendsto_const_nhds).norm).add
        (((continuous_snd.tendsto q).sub tendsto_const_nhds).norm),
  simp,
end
⟩

/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_topological_lattice {α : Type*}
  [normed_lattice_add_comm_group α] : topological_lattice α :=
topological_lattice.mk

open lattice_ordered_comm_group

variables {α : Type*} [normed_lattice_add_comm_group α]

lemma norm_sup_sub_sup_le_norm (x y z : α) : ∥x ⊔ z - (y ⊔ z)∥ ≤ ∥x - y∥ :=
solid (abs_sup_sub_sup_le_abs x y z)

lemma norm_inf_sub_inf_le_norm (x y z : α) : ∥x ⊓ z - (y ⊓ z)∥ ≤ ∥x - y∥ :=
solid (abs_inf_sub_inf_le_abs x y z)

lemma abs_pos_le (x : α) : |pos x| ≤ |x| :=
begin
  have h := abs_sup_sub_sup_le_abs x 0 0,
  simp only [sub_zero, sup_idem] at h,
  exact h,
end

lemma abs_inf_zero_le (x : α) : |x ⊓ 0| ≤ |x| :=
begin
  have h := abs_inf_sub_inf_le_abs x 0 0,
  simp only [sub_zero, inf_idem] at h,
  exact h,
end

lemma norm_sup_le_add_norm (x y : α) : ∥x ⊔ y∥ ≤ ∥x∥ + ∥y∥ :=
begin
  rw ← sub_le_iff_le_add,
  have h_norm_sub : ∥x ⊔ y - (0 ⊔ y)∥ ≤ ∥x - 0∥, from norm_sup_sub_sup_le_norm x 0 y,
  have h_sub_norm : ∥x ⊔ y∥ - ∥0 ⊔ y∥ ≤ ∥x - 0∥, from (norm_sub_norm_le _ _).trans h_norm_sub,
  rw sub_zero at h_sub_norm,
  refine le_trans _ h_sub_norm,
  refine sub_le_sub le_rfl (solid _),
  rw sup_comm,
  exact abs_pos_le _,
end

lemma norm_inf_le_add_norm (x y : α) : ∥x ⊓ y∥ ≤ ∥x∥ + ∥y∥ :=
begin
  rw ← sub_le_iff_le_add,
  have h_norm_sub : ∥x ⊓ y - (0 ⊓ y)∥ ≤ ∥x - 0∥, from norm_inf_sub_inf_le_norm x 0 y,
  have h_sub_norm : ∥x ⊓ y∥ - ∥0 ⊓ y∥ ≤ ∥x - 0∥, from (norm_sub_norm_le _ _).trans h_norm_sub,
  rw sub_zero at h_sub_norm,
  refine le_trans _ h_sub_norm,
  refine sub_le_sub le_rfl (solid _),
  rw inf_comm,
  exact abs_inf_zero_le _,
end

lemma lipschitz_with_sup_right (z : α) : lipschitz_with 1 (λ x, x ⊔ z) :=
lipschitz_with.of_dist_le_mul $ λ x y, by
{ rw [nonneg.coe_one, one_mul, dist_eq_norm, dist_eq_norm], exact norm_sup_sub_sup_le_norm x y z, }

lemma lipschitz_with_pos : lipschitz_with 1 (@lattice_ordered_comm_group.pos α _ _) :=
lipschitz_with_sup_right 0

lemma continuous_pos : continuous (@lattice_ordered_comm_group.pos α _ _) :=
lipschitz_with.continuous lipschitz_with_pos

lemma continuous_neg' : continuous (@lattice_ordered_comm_group.neg α _ _) :=
continuous_pos.comp continuous_neg

lemma pos_eq_zero_iff {E} [add_comm_group E] [lattice E] (x : E) : pos x = 0 ↔ x ≤ 0 :=
by rw [lattice_ordered_comm_group.pos, sup_eq_right]

lemma neg_eq_zero_iff {E} [add_comm_group E] [lattice E] [covariant_class E E (+) (≤)] (x : E) :
  neg x = 0 ↔ 0 ≤ x :=
by rw [neg, sup_eq_right, neg_le, neg_zero]

lemma is_closed_nonneg {E} [normed_lattice_add_comm_group E] : is_closed {x : E | 0 ≤ x} :=
begin
  suffices : {x : E | 0 ≤ x} = neg ⁻¹' {(0 : E)},
  by { rw this, exact is_closed.preimage continuous_neg' is_closed_singleton, },
  ext1 x,
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_set_of_eq, neg_eq_zero_iff x],
end

lemma is_closed_le_of_is_closed_nonneg {G} [ordered_add_comm_group G] [topological_space G]
  [has_continuous_sub G]
  (h : is_closed {x : G | 0 ≤ x}) :
  is_closed {p : G × G | p.fst ≤ p.snd} :=
begin
  have : {p : G × G | p.fst ≤ p.snd} = (λ p : G × G, p.snd - p.fst) ⁻¹' {x : G | 0 ≤ x},
    by { ext1 p, simp only [sub_nonneg, set.preimage_set_of_eq], },
  rw this,
  exact is_closed.preimage (continuous_snd.sub continuous_fst) h,
end

instance normed_lattice_add_comm_group.order_closed_topology {E} [normed_lattice_add_comm_group E] :
  order_closed_topology E :=
⟨is_closed_le_of_is_closed_nonneg is_closed_nonneg⟩
