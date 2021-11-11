/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.L_functions
import ring_theory.witt_vector.teichmuller
import ring_theory.witt_vector.compare
import data.nat.modeq
import topology.discrete_quotient
import algebra.pointwise
import data.real.basic

/-!
# Weight spaces

This file defines ... and proves ...

## Main definitions
 * `foo`
 * `bar`

## Implementation notes
TODO (optional)

## References
TODO (optional)

## Tags
p-adic, L-function, Bernoulli measure, ...
-/

--variables (A : Type*) [normed_comm_ring A] (p : ℕ) [fact p.prime] (d : ℕ) (hd : gcd d p = 1)

structure system {X : Type*} [set X] :=
( h : ℕ → finset X )
( projlim : X = Prop ) --inverse limit

def zmod.topological_space (d : ℕ) : topological_space (zmod d) := ⊥

local attribute [instance] zmod.topological_space

--instance is_this_needed : topological_space (units (zmod d) × units ℤ_[p]) := infer_instance

variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)

set_option old_structure_cmd true
/-- A-valued points of weight space -/ --shouldn't this be a category theory statement?
@[ancestor continuous_map monoid_hom]
structure weight_space extends
  monoid_hom ((units (zmod d)) × (units ℤ_[p])) A,
  C((units (zmod d)) × (units ℤ_[p]), A)
--generalize domain to a compact space?

attribute [nolint doc_blame] weight_space.to_continuous_map
attribute [nolint doc_blame] weight_space.to_monoid_hom
attribute [nolint doc_blame] weight_space.to_fun

/-lemma weight_space_continuous_to_fun {A : Type*} [topological_space A] [mul_one_class A]
  (f : weight_space p d A) : continuous f.to_fun :=
  (weight_space.to_continuous_map f).continuous_to_fun-/

example {α β : Type*} [topological_space α] [topological_space β] [group β] [topological_group β]
(f g h : α → β) [continuous f] [continuous g] [continuous h] : f*g*h = f*(g*h) :=
begin
  refine mul_assoc f g h,
end

namespace weight_space

instance : has_coe_to_fun (weight_space A p d) :=
{
  F := _,
  coe := to_fun, }

/-lemma ext_iff (A : Type*) [topological_space A] [mul_one_class A]
  (a b : (units (zmod d)) × (units ℤ_[p]) →* A) [ha : continuous a] [hb : continuous b] :
  (⟨a.to_fun, monoid_hom.map_one' a, monoid_hom.map_mul' a, ha⟩ : weight_space p d A) =
  (⟨b.to_fun, monoid_hom.map_one' b, monoid_hom.map_mul' b, hb⟩ : weight_space p d A) ↔
  a.to_fun = b.to_fun :=
begin
  split,
  { rintros h, simp only [monoid_hom.to_fun_eq_coe] at h, simp [h], },
  { rintros h, simp only [monoid_hom.to_fun_eq_coe], simp at h, simp [h], },
end-/

variables {A} {p} {d}

@[ext] lemma ext (w₁ w₂ : weight_space A p d)
  (h : ∀ u : (units (zmod d)) × (units ℤ_[p]), w₁ u = w₂ u) : w₁ = w₂ :=
begin
  cases w₁, cases w₂,
  simp, ext u,
  apply h u,
end

noncomputable instance (A : Type*) [topological_space A] [group A] [topological_group A] :
  has_one (weight_space A p d) :=
{ one := ⟨monoid_hom.has_one.one, rfl, by simp, continuous_const ⟩ }

instance (A : Type*) [topological_space A] [comm_group A] [topological_group A] :
  has_mul (weight_space A p d) :=
{ mul := λ f g, ⟨f.to_fun * g.to_fun,
    begin simp only [pi.mul_apply], repeat {rw weight_space.map_one',}, rw one_mul, end,
    λ x y, begin simp only [pi.mul_apply], repeat {rw weight_space.map_mul',},
    refine mul_mul_mul_comm (f.to_fun x) (f.to_fun y) (g.to_fun x) (g.to_fun y), end,
    -- can we pls have a tactic to solve commutativity and associativity
    continuous.mul (weight_space.continuous_to_fun f) (weight_space.continuous_to_fun g)⟩, }

noncomputable instance (A : Type*) [topological_space A] [comm_group A] [topological_group A] :
  monoid (weight_space A p d) := --is group really needed
{
  mul := (*),
  mul_assoc := λ f g h, begin ext, apply mul_assoc,
  end,
  --what is simp only doing
  one := has_one.one,
  one_mul := λ a,
  begin
    ext, apply one_mul,
  end,
  --have := one_mul a.to_fun, have h : (1 : weight_space p d A).to_fun = 1, simp only,
  --apply weight_space.mk.inj, refine one_mul a.to_fun, sorry, end,
  mul_one := λ a, begin ext, apply mul_one, end,
--  inv := λ f, ⟨λ x, (f.to_fun x)⁻¹, begin sorry end, _, _⟩,
--  mul_left_inv := sorry,
}

end weight_space

--instance : has_mod ℤ_[p] := sorry

/-lemma padic_units_modp_units (b : units ℤ_[p]) :
  is_unit ((padic_int.appr (b : ℤ_[p]) 1) : (zmod p)) :=
begin
  rw padic_int.appr,
  sorry
end

example {α β : Type*} (f : α → β) (h : function.surjective f) (b : β) : ∃ a, f a = b :=
begin
  have := h b,
  exact h b,
end

lemma blahs' (a : units ℤ_[p]) : ∃ (b : roots_of_unity (nat.to_pnat' p) ℤ_[p]),
  (a - b : ℤ_[p]) ∈ (ideal.span {p} : ideal ℤ_[p]) :=
begin
  set f : roots_of_unity (nat.to_pnat' p) ℤ_[p] → units (zmod p) :=
    λ b, classical.some (padic_units_modp_units p (b : units ℤ_[p])) with hf,
  have h : function.surjective f, sorry,
  set b := classical.some (h (classical.some (padic_units_modp_units p a))) with hb,
  refine ⟨b, _⟩,
  have h1b : padic_int.appr (a - b : ℤ_[p]) 1 = 0, sorry,
  rw ←sub_zero (a - b : ℤ_[p]),
  show (a - b : ℤ_[p]) - ((0 : ℕ) : ℤ_[p]) ∈ ideal.span {↑p}, rw ←h1b,
  have := padic_int.appr_spec 1 (a - b : ℤ_[p]), rw pow_one at this, exact this,
end

lemma blahs (a : units ℤ_[p]) : ∃ (b : units ℤ_[p]),
  (a - b : ℤ_[p]) ∈ (ideal.span {p} : ideal ℤ_[p]) :=
begin
  obtain ⟨b, hb⟩ := blahs' p a, refine ⟨(b : units ℤ_[p]), hb⟩,
end-/

/-lemma inj' {B : Type*} [monoid B] (inj : B → A) [hinj : (function.injective inj)] :
  ∃ inj' : (units B) → (units A), ∀ (x : (units B)), inj' x = inj (x : B) -/

--[fact (function.injective inj)]
variables (R : Type*) [normed_comm_ring R] [complete_space R] (inj : ℤ_[p] → R)

variables (m : ℕ) (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space R p d)
--variables (d : ℕ) (hd : gcd d p = 1) (χ : dirichlet_char_space A p d) (w : weight_space A p)
--need χ to be primitive

/-- Extending the primitive dirichlet character χ with conductor (d* p^m) -/
def pri_dir_char_extend : mul_hom ((units (zmod d)) × (units ℤ_[p])) R := sorry
--should this be def or lemma? ; units A instead of A ; use monoid_hom instead of mul_hom
-- so use def not lemma, because def gives Type, lemma gives Prop

--variables (ψ : pri_dir_char_extend A p d)

/-- The Teichmuller character defined on `p`-adic units -/
--noncomputable def teichmuller_character (a : units ℤ_[p]) : R := inj (classical.some (blahs p a))
noncomputable def teichmuller_character : monoid_hom (units ℤ_[p]) ℤ_[p] :=
{
  to_fun := λ a,
    witt_vector.equiv p (witt_vector.teichmuller_fun p (padic_int.to_zmod (a : ℤ_[p]))),
  ..monoid_hom.comp (witt_vector.equiv p).to_monoid_hom
  (monoid_hom.comp (witt_vector.teichmuller p)
    (monoid_hom.comp (padic_int.to_zmod).to_monoid_hom
      ⟨(coe : units ℤ_[p] → ℤ_[p]), units.coe_one, units.coe_mul⟩)),
}

lemma unit_to_zmod_nonzero (a : units ℤ_[p]) :
  (padic_int.to_zmod (a : ℤ_[p]))^(p - 1) = (1 : (zmod p)) :=
begin
  apply zmod.pow_card_sub_one_eq_one,
  by_contra, push_neg at h,
  have h' : (a : ℤ_[p]) ∈ padic_int.to_zmod.ker,
  { exact padic_int.to_zmod.mem_ker.mpr h, },
  rw [padic_int.ker_to_zmod, local_ring.mem_maximal_ideal, mem_nonunits_iff] at h',
  apply h', simp,
end

lemma teichmuller_character_root_of_unity (a : units ℤ_[p]) :
  (teichmuller_character p a)^(p - 1) = 1 :=
begin
  have : (padic_int.to_zmod (a : ℤ_[p]))^(p - 1) = (1 : (zmod p)),
  exact unit_to_zmod_nonzero p a, --rw witt_vector.from_padic_int,
  rw [←monoid_hom.map_pow, teichmuller_character, monoid_hom.coe_mk, units.coe_pow],
  simp only [this, ring_hom.map_pow, ring_equiv.map_eq_one_iff],
  have f := monoid_hom.map_one (witt_vector.teichmuller p), refine f,
end

variables (p)

def clopen_basis : set (set ℤ_[p]) := {x : set ℤ_[p] | ∃ (n : ℕ) (a : zmod (p^n)),
  x = set.preimage (padic_int.to_zmod_pow n) {a} }

lemma span_eq_closed_ball (n : ℕ) :
  metric.closed_ball 0 (1/p^n) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext, simp, rw ←padic_int.norm_le_pow_iff_mem_span_pow, simp,
end

lemma is_closed_span (n : ℕ) : is_closed (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  rw ←span_eq_closed_ball, exact metric.is_closed_ball,
end

lemma span_eq_open_ball (n : ℕ) :
  metric.ball 0 ((p : ℝ) ^ (1 - (n : ℤ))) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext, simp only [mem_ball_zero_iff, set_like.mem_coe],
  rw [←padic_int.norm_le_pow_iff_mem_span_pow, padic_int.norm_le_pow_iff_norm_lt_pow_add_one],
  have : 1 - (n : ℤ) = -(n : ℤ) + 1 := sub_eq_neg_add 1 ↑n,
  rw this,
end

lemma is_open_span (n : ℕ) : is_open ((ideal.span {p ^ n} : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
  rw ←span_eq_open_ball,
  exact metric.is_open_ball,
end

lemma continuous_of_topological_basis {α β : Type*} {B : set (set β)} [topological_space α]
  [topological_space β] (f : α → β) (hB : topological_space.is_topological_basis B)
  (h : ∀ s ∈ B, is_open (f⁻¹' s)) : continuous f :=
begin
  refine {is_open_preimage := _}, rintros t ht,
  obtain ⟨S, hS, tsUnion⟩ := topological_space.is_topological_basis.open_eq_sUnion hB ht,
  rw tsUnion, simp, apply is_open_Union, rintros i, apply is_open_Union, intro memi,
  exact h i (hS memi),
end

lemma discrete_topology.is_topological_basis
  {α : Type*} [topological_space α] [discrete_topology α] [monoid α] :
  @topological_space.is_topological_basis α _ (set.range set.singleton_hom) :=
begin
  refine topological_space.is_topological_basis_of_open_of_nhds _ _,
  { simp, },
  rintros a u mema openu,
  refine ⟨({a} : set α), _, _, _⟩,
  { simp, use a, rw set.singleton_hom, simp, },
  { simp, },
  simp [mema],
end

open padic_int

/-example (a b n : ℕ) (h : b ≤ a) : (a : zmod n) - (b : zmod n) = (((a - b) : ℕ) : zmod n) :=
begin
  norm_cast at *,
end

lemma eq_zero_of_dvd_of_lt' {a b c : ℕ} (w : a ∣ (b - c)) (h : b < a) : b - c = 0 :=
begin
  have f := nat.eq_zero_of_dvd_of_div_eq_zero w, apply f,
  have h' : b - c < a, sorry,
  rw nat.div_eq_zero_iff _, { exact h', },
  apply lt_of_le_of_lt _ h', simp,
end

lemma preimage_to_zmod_pow_eq_ball (n : ℕ) (x : ℕ) :
  (padic_int.to_zmod_pow n) ⁻¹' {(x : zmod (p^n))} =
  metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
begin
  ext y,
  simp only [set.mem_preimage, metric.mem_ball, set.mem_singleton_iff],
  rw [dist_eq_norm, sub_eq_neg_add 1 (n : ℤ), ←norm_le_pow_iff_norm_lt_pow_add_one,
    padic_int.norm_le_pow_iff_mem_span_pow], dsimp [to_zmod_pow, to_zmod_hom],
  split,
  { intro h, convert appr_spec n y,
    have := le_total x (appr y n), cases this,
    { rw ←sub_eq_zero at h,
      have h' : ((((y.appr n) - x) : ℕ) : zmod (p^n)) = 0,
      { norm_cast at *, exact h, },
      rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h',
      have h'' := eq_zero_of_dvd_of_lt' h' (appr_lt _ _),
      rw nat.sub_eq_zero_iff_le at h'', refine antisymm this h'', },
    { symmetry' at h, rw ←sub_eq_zero at h,
      have h' : (((x - (y.appr n)) : ℕ) : zmod (p^n)) = 0,
      { norm_cast at *, exact h, },
      rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h',
      have h'' := eq_zero_of_dvd_of_lt' h' (appr_lt _ _),
      rw nat.sub_eq_zero_iff_le at h'', refine antisymm this h'', },
    rw zmod.nat_coe_eq_nat_coe_iff at h, rw nat.modeq.modeq_iff_dvd at h,
    --apply int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs,
    sorry, },
  { intro h, apply zmod_congr_of_sub_mem_span n y _ _ _ h, apply appr_spec n y, },
end
--is there a nicer way of doing this using translation properties and x = 0?
-/

-- enable set addition for additive groups
open_locale pointwise

lemma preimage_to_zmod_pow (n : ℕ) (x : zmod (p^n)) : (to_zmod_pow n) ⁻¹' {x} =
 {(x : ℤ_[p])} + (((to_zmod_pow n).ker : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
 ext y,
    simp only [set.image_add_left, set.mem_preimage, set.singleton_add,
      set.mem_singleton_iff, set_like.mem_coe],
    split,
    { intro h, rw ring_hom.mem_ker, simp [h], },
    { intro h, rw ring_hom.mem_ker at h, simp at *, rw neg_add_eq_zero at h, exact h.symm, },
end

lemma continuous_to_zmod_pow (n : ℕ) : continuous (@padic_int.to_zmod_pow p _ n) :=
begin
  refine continuous_of_topological_basis _ discrete_topology.is_topological_basis _,
  rintros s hs, simp only [set.mem_range] at hs, cases hs with x hx,
  change {x} = s at hx, rw ←hx,
  rw [preimage_to_zmod_pow, ker_to_zmod_pow],
  refine is_open.add_left _, exact is_open_span p n,
end

lemma proj_lim_preimage_clopen (n : ℕ) (a : zmod (d*(p^n))) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
begin
  split,
  { refine continuous_def.mp (continuous_to_zmod_pow p n) {a} trivial, },
  { refine continuous_iff_is_closed.mp (continuous_to_zmod_pow p n) {a} _, simp, },
end

example {α : Type*} [h : has_add α] : has_add (set α) := by refine set.has_add

lemma add_ball (x y : ℤ_[p]) (r : ℝ) :
  ({x} : set ℤ_[p]) + metric.ball y r = metric.ball (x + y) r :=
begin
  ext z, simp,
  have : dist (-x + z) y = dist z (x + y),
  { rw dist_eq_norm, rw dist_eq_norm, apply congr_arg, ring, },
  rw this,
end

lemma preimage_to_zmod_pow_eq_ball (n : ℕ) (x : zmod (p^n)) :
  (padic_int.to_zmod_pow n) ⁻¹' {(x : zmod (p^n))} =
  metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
begin
  rw preimage_to_zmod_pow, rw ker_to_zmod_pow, rw ←span_eq_open_ball, rw add_ball,
  rw add_zero,
end

lemma is_clopen_prod {α β : Type*} [topological_space α] [topological_space β] {s : set α}
  {t : set β} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s.prod t) :=
begin
  split,
  { rw is_open_prod_iff', fconstructor, refine ⟨(hs).1, (ht).1⟩, },
  { apply is_closed.prod (hs).2 (ht).2, },
end

lemma is_clopen_singleton {α : Type*} [topological_space α] [discrete_topology α] (b : α) :
  is_clopen ({b} : set α) :=
 ⟨is_open_discrete _, is_closed_discrete _⟩

def clopen_from (n : ℕ) (a : zmod (d * (p^n))) : clopen_sets (zmod d × ℤ_[p]) :=
⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩

@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }

example (n : ℕ) (a : zmod (d * (p^n))) : clopen_basis' p d :=
⟨clopen_from p d n a, ⟨n, a, rfl⟩⟩

example (U : clopen_basis' p d) : clopen_sets (zmod d × ℤ_[p]) := U.val

-- lemma mem_clopen_basis' (U : clopen_sets ((zmod d) × ℤ_[p])) (hU : U ∈ clopen_basis' p d) :
--   ∃ (n : ℕ) (a : zmod (d * (p^n))),
--   U = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
--     is_clopen_prod (is_clopen_singleton (a : zmod d))
--       (proj_lim_preimage_clopen p d n a) ⟩ := sorry

/-def clopen_basis' : set (clopen_sets ((zmod d) × ℤ_[p])) :=
{x : clopen_sets ((zmod d) × ℤ_[p]) | ∃ (n : ℕ) (a : zmod (p^n)) (b : zmod d),
  x = ⟨({b} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) a),
    is_clopen_prod (is_clopen_singleton b) (proj_lim_preimage_clopen p n a) ⟩ }-/


lemma find_this_out (ε : ℝ) (h : 0 < ε) : ∃ (n : ℕ), (1 / (p^n) : ℝ) < ε :=
begin
  convert exists_pow_lt_of_lt_one h _, swap, exact 1/p,
  { simp only [one_div, inv_pow'], },
  rw div_lt_iff _, { simp, apply nat.prime.one_lt, apply fact_iff.1 _, assumption, },
  simp, apply nat.prime.pos, apply fact_iff.1 _, assumption,
end

lemma mem_clopen_basis (n : ℕ) (a : zmod (p^n)) :
  (padic_int.to_zmod_pow n)⁻¹' {a} ∈ (clopen_basis p) := ⟨n, a, rfl⟩

--example {α : Type*} (x : α) : x ∈ (x : set α) :=

--lemma mem_clopen_basis'
--∃ (n : ℕ) (a : zmod (p^n)), x = set.preimage (padic_int.to_zmod_pow n) a

lemma has_coe_t_eq_coe (a : ℤ_[p]) (n : ℕ) : ((to_zmod_pow n a) : ℤ_[p]) = a.appr n :=
begin
  dsimp [to_zmod_pow, to_zmod_hom], rw ←zmod.nat_cast_comp_val ℤ_[p],
  { simp, apply zmod.val_cast_of_lt (appr_lt _ _), },
  exact fact.pow.pos,
end

lemma dist_appr_spec (a : ℤ_[p]) (n : ℕ) : dist a ((a.appr n) : ℤ_[p]) ≤ (p : ℝ)^(-n : ℤ) :=
begin
  rw dist_eq_norm,
  have := appr_spec n a,
  rw ←norm_le_pow_iff_mem_span_pow at this, exact this,
end

example (a b c : ℤ) (h1 : a < c) (h2 : b ≤ d) : a + b < c + d := add_lt_add_of_lt_of_le h1 h2

example (m : ℕ) : 1/((p : ℝ)^m) = ((p^m) : ℝ)⁻¹ := one_div (↑p ^ m)

theorem clopen_basis_clopen : topological_space.is_topological_basis (clopen_basis p) ∧
  ∀ x ∈ (clopen_basis p), is_clopen x :=
begin
  split,
  { refine topological_space.is_topological_basis_of_open_of_nhds _ _,
    { rintros u hu, rcases hu with ⟨n, a, hu⟩,
      have := proj_lim_preimage_clopen p 1 n,
      rw one_mul at this, rw hu, convert (this a).1, simp, },
    rintros a u mema hu, rw metric.is_open_iff at hu,
    obtain ⟨ε, hε, h⟩ := hu a mema,
    obtain ⟨m, fm⟩ := find_this_out p (ε/2) (half_pos hε),
    set b := ((to_zmod_pow m.succ a) : ℤ_[p]) with hb,
    refine ⟨metric.ball b (p^(-(m : ℤ))), _, _, _⟩,
    dsimp [to_zmod_pow, to_zmod_hom] at hb,
    { have arith : -(m : ℤ) = 1 - (m.succ : ℤ), simp, linarith,
      rw [arith],
      rw ←preimage_to_zmod_pow_eq_ball p (m.succ) (to_zmod_pow m.succ a),
      convert mem_clopen_basis p m.succ ((to_zmod_pow m.succ) a), },
    { simp only [metric.mem_ball], rw dist_eq_norm, rw hb,
      rw has_coe_t_eq_coe p a m.succ,
      have := appr_spec m.succ a, rw ←norm_le_pow_iff_mem_span_pow _ m.succ at this,
      refine gt_of_gt_of_ge _ this,
      repeat{rw fpow_neg, rw ←one_div,},
      apply one_div_lt_one_div_of_lt, norm_num, convert pow_pos _ m, simp, sorry, sorry, },
    { rintros c hc, apply h, simp at hc, simp,
      suffices f1 : dist c a < 2 / (p^m),
      { refine lt_trans f1 _, simp [fm], refine (lt_div_iff' _).mp _, exact zero_lt_two,
        rw ←one_div, exact fm, },
      have := dist_triangle c b a, rw dist_comm b a at this, refine gt_of_gt_of_ge _ this,
      have ha : dist a b ≤ (↑p ^ m)⁻¹,
      { rw hb, rw has_coe_t_eq_coe p a m.succ,
        have : (↑p ^ m)⁻¹ = (p : ℝ)^(-m : ℤ), sorry,
        rw this, refine le_trans (dist_appr_spec p a m.succ) _, sorry, },
      convert add_lt_add_of_lt_of_le hc ha,
      rw [←one_div, div_add_div_same, one_add_one_eq_two], }, },
  { rintros x hx,
    rw clopen_basis at hx, simp at hx, rcases hx with ⟨n, a, hx⟩, rw hx,
    have := proj_lim_preimage_clopen p 1 n, rw one_mul at this, convert this a, simp, },
end

--lemma char_fn_basis_of_loc_const : is_basis A (@char_fn ℤ_[p] _ _ _ _ A _ _ _) := sorry

--instance : semimodule A (units ℤ_[p]) := sorry
-- a + pZ_p a from0 to (p - 2) [for linear independence]
-- set up a bijection between disj union
-- construct distri prove eval at canonical basis gives (a,n)

variables {c : ℕ}

--def clopen_nat_equiv : clopen_basis' p d ≃ (ℕ → )

def E_c (hc : gcd c p = 1) := λ (n : ℕ) (a : (zmod (d * (p^n)))), fract ((a.val : ℚ) / (d*p^n))
    - c * fract ( (((((c : zmod (d * p^(2 * n)))⁻¹ : zmod (d * p^n)) * a) : zmod (d * p^n)) : ℚ) / (d * p^n)) + (c - 1)/2

-- I don't understand why this works!
example (n : ℕ) (a b : zmod n) : ((a * b) : ℚ) = (a : ℚ) * (b : ℚ) :=
begin
  have : zmod n → ℤ, exact zmod.val_min_abs,
  rw coe_to_lift,
end
--instance {α : Type*} [topological_space α] : semimodule A (locally_constant α A) := sorry

example (x : ℕ) : ((x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) :=
coe_coe x

example (m : ℕ) : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m) :=
begin
  rw ←add_div, refl,
end

instance [fact (0 < d)] : compact_space (zmod d) := fintype.compact_space
--instance : totally_bounded (set.univ ℤ_[p]) :=
instance : compact_space ℤ_[p] :=
begin
  refine is_compact_iff_compact_space.mp _,
  rw compact_iff_totally_bounded_complete,
  split,
  {
    refine metric.totally_bounded_of_finite_discretization _,
    rintros ε hε,
    obtain ⟨m, fm⟩ := find_this_out p (ε/2) (half_pos hε),
    have fm' : (2 : ℝ)/(p^m) < ε, sorry,
    refine ⟨zmod (p^m.succ), _, to_zmod_pow m.succ, λ x y h, _ ⟩,
    { have : fact (0 < (p^(m.succ))), { exact fact.pow.pos, },
      apply zmod.fintype _, assumption, },
    apply lt_trans _ fm',
    rw ←set.mem_singleton_iff at h, rw ←set.mem_preimage at h,
    rw preimage_to_zmod_pow_eq_ball at h, rw metric.mem_ball at h,
    rw has_coe_t_eq_coe at h,
    refine gt_of_gt_of_ge _ (dist_triangle x (appr y m.succ) y),
    have f : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m), {  rw ←add_div, refl, },
    rw f, rw dist_comm _ ↑y,
    have f' : ↑p ^ (1 - (m.succ : ℤ)) = (1 : ℝ) / (p^m), sorry, rw f' at h,
    rw add_comm (dist _ _) _,
    have f'' : ↑p ^ -(m.succ : ℤ) < (1 : ℝ) / (p^m),
    { rw div_eq_inv_mul, rw mul_one, rw fpow_neg, rw inv_lt_inv,
      { simp, rw fpow_add, simp, rw ←mul_one ((p : ℝ)^m), rw mul_comm, rw mul_comm _ (p : ℝ), apply mul_lt_mul,
          { norm_cast, apply nat.prime.one_lt, rw fact_iff at *, assumption, },
          { rw one_mul, },
          { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, },
          { norm_cast, exact zero_le p, },
        { exact nonzero_of_invertible ↑p, }, },
      { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, },
      { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, }, },
    have := add_lt_add (gt_of_gt_of_ge f'' (ge_iff_le.2 (dist_appr_spec p y (m.succ)))) h,
    rw [subtype.dist_eq y _, subtype.dist_eq x _, padic_int.coe_coe] at this,
    exact this, },
  { refine complete_space_coe_iff_is_complete.mp _,
    show complete_space ℤ_[p],
    apply_instance, },
end
--better way to do it? maybe without showing totally bounded (should that be a separate lemma?)?
-- better stick to either div or inv. which is easier to work with?

--instance [fact (0 < d)] : compact_space (zmod d × ℤ_[p]) := infer_instance
instance : totally_disconnected_space ℤ_[p] :=
begin
  rw compact_t2_tot_disc_iff_tot_sep,
  refine {is_totally_separated_univ := _},
  rintros x hx y hx ne,
  obtain ⟨n,hn⟩ : ∃ (n : ℕ), to_zmod_pow n x ≠ to_zmod_pow n y,
  { contrapose ne, push_neg at ne, rw ext_of_to_zmod_pow at ne, simp [ne], },
  have f : is_totally_separated (set.univ : set (zmod (p^n))),
  { exact totally_separated_space.is_totally_separated_univ (zmod (p ^ n)), },
  obtain ⟨u, v, hu, hv, memu, memv, univ, disj⟩ :=
    f (to_zmod_pow n x) (set.mem_univ _) (to_zmod_pow n y) (set.mem_univ _) hn,
  refine ⟨(to_zmod_pow n)⁻¹' u, (to_zmod_pow n)⁻¹' v,
    continuous_def.mp (continuous_to_zmod_pow p n) u hu,
    continuous_def.mp (continuous_to_zmod_pow p n) v hv,
    set.mem_preimage.mpr memu, set.mem_preimage.mpr memv,
    λ z hz, _, _⟩,
  { rw set.mem_union,
    have univ' := univ (set.mem_univ (to_zmod_pow n z)),
    cases univ',
    { left, apply set.mem_preimage.mpr univ', },
    { right, apply set.mem_preimage.mpr univ', }, },
  { ext z, rw ←@set.preimage_empty _ _ (to_zmod_pow n), rw set.mem_preimage,
    rw set.ext_iff at disj, specialize disj (to_zmod_pow n z), simp [disj], simp at disj,
    assumption, },
end
--ℤ_[p] is now profinite!
--instance sigh : totally_disconnected_space (zmod d × ℤ_[p]) := infer_instance

/-
@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }
-/
variables [fact (0 < d)]
def bernoulli_measure (hc : gcd c p = 1) [has_coe ℝ R] :=
{x : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R |
  ∀ (n : ℕ) (a : zmod (d * (p^n))), x (char_fn (zmod d × ℤ_[p]) ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩) =
    E_c p d hc n a }

/-
@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }
-/
variables (d)

open_locale big_operators

-- lemma what_to_do (f : locally_constant (zmod d × ℤ_[p]) R) : ∃ (s : finset ℕ)
--   (j : s → R) (i : s → (clopen_basis' p d)), f = ∑ k : s, j(k) • (char_fn (zmod d × ℤ_[p]) (i k)) :=
-- begin
--   sorry,
-- end

-- /-- To define a linear map on locally constant functions, it is sufficient to define it for
--   characteristic functions on the topological basis `clopen_basis'`. -/
-- noncomputable lemma pls_work (f : clopen_basis' p d → R) : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R :=
-- begin
-- constructor, swap 3,
-- { intro g,
--   set s := classical.some (what_to_do p d R g) with hs,
--  --     have hs := classical.some_spec (what_to_do p d R f),
--   set i := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R g))) with hi,
--   set j := classical.some (classical.some_spec (what_to_do p d R g)) with hj,
--   have hs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R g))),
--   exact ∑ k : s, j(k) * f(i(k)), },
--   { sorry, },
--   sorry,
-- end

--import linear_algebra.finsupp
variables (R' M N : Type*) [ring R'] [add_comm_group M] [add_comm_group N]
  [module R' M] [module R' N] (S : set M)

lemma mem_nonempty {α : Type*} {s : set α} {x : α} (h : x ∈ s) : nonempty s := ⟨⟨x, h⟩⟩

instance : is_absolute_value (norm : R → ℝ) :=
begin
  constructor, repeat {simp,}, refine norm_add_le, sorry,
end

/-instance partial_order_R : partial_order R :=
begin
  fconstructor,
  exact λ a b, true,
  repeat {simp,},
end-/

def is_eventually_constant {α : Type*} (a : ℕ → α) : Prop :=
 { n | ∀ m, n ≤ m → a (nat.succ m) = a m }.nonempty

structure eventually_constant_seq {α : Type*} :=
(to_seq : ℕ → α)
(is_eventually_const : is_eventually_constant to_seq)

noncomputable def sequence_limit_index' {α : Type*} (a : @eventually_constant_seq α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a.to_seq m.succ = a.to_seq m }

noncomputable def sequence_limit_index {α : Type*} (a : ℕ → α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a n = a m }

noncomputable def sequence_limit {α : Type*} (a : @eventually_constant_seq α) :=
a.to_seq (sequence_limit_index' a)

lemma sequence_limit_eq {α : Type*} (a : @eventually_constant_seq α) (m : ℕ)
  (hm : sequence_limit_index' a ≤ m) : sequence_limit a = a.to_seq m := sorry

def equi_class (n m : ℕ) (h : n < m) (a : zmod (d * p^n)) :=
 {b : zmod (d * p^m) | (b : zmod (d * p^n)) = a}
-- change def to a + k*dp^m

lemma mem_equi_class (n m : ℕ) (h : n < m) (a : zmod (d * p^n)) (b : zmod (d * p^m)) :
  b ∈ equi_class p d n m h a ↔ (b : zmod (d * p^n)) = a :=
⟨λ hb, begin rw equi_class at hb, simp at hb, exact hb, end,
  λ hb, begin rw equi_class, simp, exact hb, end⟩

instance (n m : ℕ) (h : n < m) (a : zmod (d * p^n)) : fintype (equi_class p d n m h a) := sorry

/-- For m > n, E_c(χ_(b,a,n)) = ∑_{j, b_j = a mod p^n} E_c(χ_(b,b_j,m)) -/
lemma sum_char_fn_dependent_Ec (m : ℕ) (a : zmod (p^m)) (b : zmod d) (hc : gcd c p = 1) :
  E_c p d hc m a = ∑ x in set.to_finset (equi_class p d m m.succ (lt_add_one m) a), E_c p d hc m.succ x :=
sorry

lemma loc_const_const (f : locally_constant (zmod d × ℤ_[p]) R) (a : zmod d × ℤ_[p]) : ∃ N : ℕ, ∀ m ≥ N,
  ∀ y ∈ {b : zmod d × ℤ_[p] | (to_zmod_pow m) a.2 = (to_zmod_pow m) b.2}, f y = f a :=
sorry

lemma remove_extras (x : zmod d × ℤ_[p]) (n : ℕ) :
  is_clopen {b : zmod d × ℤ_[p] | (to_zmod_pow n) x.snd = (to_zmod_pow n) b.snd ∧ x.fst = b.fst} :=
sorry

noncomputable def F : ℕ → discrete_quotient (zmod d × ℤ_[p]) := λ n,
  ⟨λ a b, to_zmod_pow n a.2 = to_zmod_pow n b.2 ∧ a.1  = b.1,
    ⟨ by tauto, by tauto, λ a b c hab hbc, begin simp at *, split, rw [hab.1, hbc.1], rw [hab.2, hbc.2], end⟩,
    λ x, begin apply remove_extras p d x n,
--      convert_to is_clopen ((({x.1} : set (zmod d)) × (set.preimage (to_zmod_pow n) {to_zmod_pow n x.2})) : set ((zmod d) × ℤ_[p])),
--      { ext1 y, simp, split; try { intro h, rw set.mem_singleton_iff at *, rw h, }, },
--      { convert proj_lim_preimage_clopen p 1 n (to_zmod_pow n x), rw one_mul, simp, },
end⟩

/-lemma loc_const_const' (f : locally_constant (zmod d × ℤ_[p]) R) : ∃ N : ℕ, ∀ m ≥ N,
  ∀ y ∈ {b : zmod d × ℤ_[p] | (to_zmod_pow m) a.2 = (to_zmod_pow m) b.2}, f y = f a :=
sorry-/

lemma factor_F (f : locally_constant (zmod d × ℤ_[p]) R) :
  ∃ N : ℕ, F p d N ≤ f.discrete_quotient := sorry

example {α : Type*} [h : fintype α] : fintype (@set.univ α) := by refine set_fintype set.univ

lemma mul_prime_pow_pos (m : ℕ) : 0 < d * p^m :=
begin
  rw fact_iff at *,
  refine mul_pos _ _,
  { assumption, },
  { apply pow_pos (nat.prime.pos _), assumption, },
end

def zmod' (n : ℕ) (h : 0 < n) : finset (zmod n) :=
  @finset.univ _ (@zmod.fintype n (fact_iff.2 h))

--def zmod' (n : ℕ) (h : fact (0 < n)) : finset (zmod n) :=
--  @set.to_finset _ (@set.univ (zmod n)) (@set_fintype _ (@zmod.fintype n h) set.univ _)

lemma succ_eq_bUnion_equi_class : zmod' (d*p^m.succ) (mul_prime_pow_pos p d m.succ) =
  (zmod' (d*p^m) (mul_prime_pow_pos p d m)).bUnion
    (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a)) :=
sorry

lemma equi_class_eq (f : locally_constant (zmod d × ℤ_[p]) R) (x : zmod (d * p^m))
  (y : zmod (d * p^m.succ))
  (hy : y ∈ ((λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a)) x)) :
  f y = f x := sorry

lemma fract_eq_self {a : ℚ} (h : 0 ≤ a) (ha : a < 1) : fract a = a :=
begin
   rw fract_eq_iff,
   refine ⟨h, ha, ⟨0, _⟩⟩, simp,
end

lemma equi_class_some (n : ℕ) (x : zmod (d * p^n)) (y : equi_class p d n n.succ (lt_add_one n) x) :
  ∃ k : ℕ, k < p ∧ (y : zmod (d * p^n.succ)).val = x.val + k * d * p^n :=
begin
  have := (mem_equi_class p d n n.succ (lt_add_one n) x y).1 (y.prop),
  conv { congr, funext, conv { congr, skip, to_rhs, rw ←((mem_equi_class p d n n.succ (lt_add_one n) x y).1 (y.prop)), }, },
  rw ←@zmod.nat_cast_comp_val _ _ _ _,
  show ∃ (k : ℕ), k < p ∧ (y : zmod (d * p^n.succ)).val = ((y : zmod (d * p^n.succ)).val : zmod (d * p^n)).val + k * d * p ^ n,
  rw zmod.val_nat_cast,
  use (y : zmod (d * p^n.succ)).val / (d * p^n), split,
  { apply nat.div_lt_of_lt_mul, rw nat.mul_assoc,
    rw ←pow_succ',
    apply @zmod.val_lt _ (fact_iff.2 _) (y : zmod (d * p^n.succ)),
    apply mul_pos, rw fact_iff at *, assumption,
    apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, },
  { rw mul_assoc,
    rw nat.mod_add_div' (y : zmod (d * p^n.succ)).val (d * p^n), },
  { rw fact_iff at *,
    apply mul_pos, rw fact_iff at *, assumption,
    apply pow_pos, apply nat.prime.pos, assumption, },
end

lemma coe_addd (m : ℕ) (b c : zmod (d * p^m.succ)) : (b + c : zmod (d * p^m)) = (b : zmod (d * p^m)) + (c : zmod (d * p^m)) :=
begin
  simp only [eq_self_iff_true],
end
-- (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m))
lemma maybe_generalize (m : ℕ) : (coe : zmod (p^(m.succ)) → zmod (p^m)) ∘ (coe : zmod (p^m) → zmod (p^(m.succ))) = id :=
begin
 ext x,
  simp only [id.def, function.comp_app],
  have : p^m ∣ (p^(m+1)),
  { apply pow_dvd_pow, simp, },
  rw ← @zmod.nat_cast_val (p^m) _ _ (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m)) x,
  conv_rhs {
    rw ← zmod.cast_id (p^m) x,
    rw ← @zmod.nat_cast_val (p^m) _ _ (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m)) x, },
  exact zmod.cast_nat_cast this x.val,
end

lemma val_coe_eq_val (n m : ℕ) (b : zmod n) [h1 : fact (0 < n)] [h2 : n < m] : (b.val : zmod m).val = b.val :=
begin
  have : b.val = (b : zmod m).val,
  { have h1 := zmod.val_lt b,
    have h2 : b.val < m, { transitivity n, assumption, assumption, },
    have := zmod.val_cast_of_lt h2, rw ←this, apply congr_arg, simp, },
  conv_rhs { rw this, },
  apply congr_arg, rw @zmod.nat_cast_val _ _ _ _ _, assumption,
end

example (a b c d : ℕ) (h : a ≤ b) : a < b.succ :=
begin
  exact nat.lt_succ_iff.mpr h,
end

def equi_iso_fin (m : ℕ) (a : zmod (d * p^m)) : equi_class p d m m.succ (lt_add_one m) a ≃ fin p :=
{ to_fun := λ y, ⟨((y.val).val - a.val) / (d * p^m), begin
    apply nat.div_lt_of_lt_mul,
    have : 0 < d * p ^ m.succ,
      rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) _), assumption,
    have := @zmod.val_lt _ (fact_iff.2 this) y.val,
    rw [mul_assoc, ←pow_succ'],
    have f := nat.sub_le (y.val).val a.val,
    exact lt_of_le_of_lt f this,
end⟩,
  inv_fun := λ k, ⟨(a.val + k * d * p^m : ℕ), begin
    rw mem_equi_class,
    have g : (d * (p^m)) ∣ (d * p^(m.succ)),
    { apply mul_dvd_mul,
      { refl, },
      { rw pow_succ' p m, exact dvd.intro p rfl, }, },
    rw zmod.cast_nat_cast g, swap, exact zmod.char_p (d * p ^ m),
    rw nat.cast_add,
    rw @zmod.nat_cast_zmod_val _ _ _, swap,
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m), assumption, },
      rw mul_assoc,
      simp,
  end⟩,
  left_inv := begin
    rintros x,
    rw subtype.ext_iff_val, simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    rw mul_assoc,
    obtain ⟨k, hk, h⟩ := equi_class_some p d m a x,
    rw nat.div_mul_cancel,
    { have : fact (0 < d * p ^ m.succ),
      { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m.succ), assumption, },
      rw nat.add_sub_cancel',
      { rw @zmod.nat_cast_val _ _ _ this _, norm_cast, },
      { rw h, apply nat.le_add_right, }, },
    { rw [h, nat.add_sub_cancel_left, mul_assoc], simp, },
  end,
  right_inv := begin
    rintros x,
    simp only [nat.cast_pow],
    rw subtype.ext_iff_val,
    simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    have : fact (0 < d * p ^ m.succ),
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m.succ), assumption, },
    have h2 : fact (0 < d * p ^ m),
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m), assumption, },
    apply nat.div_eq_of_eq_mul_left,
    { apply fact_iff.1 h2, },
    apply nat.sub_eq_of_eq_add,
    rw [mul_assoc, zmod.val_nat_cast, nat.mod_eq_of_lt],
    have h1 := @zmod.val_lt _ h2 a,
    have h2 : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
    { rw mul_comm, apply nat.mul_le_mul_left, rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel], apply x.2,
      { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, },
    have := add_lt_add_of_lt_of_le h1 h2,
    convert this,
    ring_nf, rw nat.sub_add_cancel,
    { rw ←pow_succ, },
    { apply le_of_lt, apply fact_iff.1 (nat.prime.one_lt' p), },
  end }

lemma sum_equiv {α β γ : Type*} {s : finset α} {s' : finset β} {φ : s ≃ s'} {f : α → γ}
  [add_comm_monoid γ] : ∑ x : s, f x = ∑ y : s', f(φ.inv_fun y) :=
begin
  apply finset.sum_bij',
  swap 4, rintros, exact φ.to_fun a,
  swap 5, rintros, exact φ.inv_fun a,
  all_goals {simp},
end

lemma why_no_find (a b : ℤ) : a = b ↔ a.succ = b.succ :=
begin
  split,
  exact congr_arg (λ (a : ℤ), a.succ),
  rintros, rw int.succ at *, rw int.succ at *, simp at *, assumption,
end

lemma this_must_exist (n : ℕ) [fact (0 < n)] (a : zmod n) : (a.val : ℤ) = (a : ℤ) :=
begin
  rw ←zmod.nat_cast_val a, congr, rw nat.cast_coe, rw coe_base,
  congr, ext, rw coe_b,
  induction x,
  { norm_num, change int.of_nat 0 = _, change int.of_nat 0 = (0 : ℤ), simp, },
  { norm_num, change int.of_nat x_n.succ = _, change (int.of_nat x_n).succ = _,
    rw why_no_find at x_ih, convert x_ih, },
end

lemma zmod_int_add (n : ℕ) [fact (0 < n)] (a b : zmod n) : (((a + b) : zmod n) : ℤ) = (a + (b : ℤ)) % n :=
begin
  rw [←this_must_exist, zmod.val_add],
  simp only [int.coe_nat_add, int.coe_nat_mod],
  apply congr_fun,
  apply congr_arg,
  rw [←this_must_exist, ←this_must_exist],
end

example (n : ℕ) (h : 0 < n) : n ≠ 0 := ne_of_gt h

lemma sum_fract (m : ℕ) [0 < m] (x : zmod (d * p^m)) : ∑ (x_1 : (equi_class p d m m.succ (lt_add_one m) x)),
  fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) =
    (x.val : ℚ) / (d * p^m) + (p - 1) / 2 :=
begin
  haveI imp : ∀ n : ℕ, fact (0 < d * p^n), sorry,
  have : ∀ (n : ℕ) (x : zmod (d * p^n)), 0 ≤ (x.val : ℚ) / (d * p^n) ∧ (x.val : ℚ) / (d * p^n) < 1,
  sorry,
  conv_lhs { congr, skip, funext, rw [fract_eq_self ((this m.succ x_1).1) ((this m.succ x_1).2)], },
  rw fintype.sum_equiv (equi_iso_fin p d m x),
  swap 3, { intro k, exact ↑((equi_iso_fin p d m x).inv_fun k).val / (d * p ^ m.succ), },
  { rw ←finset.sum_div,
    have : ∀ k : fin p, ((equi_iso_fin p d m x).inv_fun k).val = x.val + ↑k * (d * p^m),
    { simp, sorry, },
    conv_lhs { congr, congr, skip, funext, rw this x, rw ←zmod.int_cast_cast,
      rw zmod.coe_add_eq_ite, rw ←ite_not, }, push_neg,
    convert_to (∑ x_1 : fin p, ((((x.val) : zmod (d * p^m.succ)) : ℤ) +
      (↑x_1 * ((d : zmod (d * p^m.succ)) * (p : zmod (d * p^m.succ)) ^ m) : ℤ) : ℚ)) / _ = _,
    { congr, ext y, norm_cast, split_ifs,
      { congr, simp, sorry, },
      { exfalso, apply h, sorry, }, },
    { rw finset.sum_add_distrib, rw finset.sum_const, rw finset.card_univ, rw fintype.card_fin _,
      norm_cast, rw ←finset.sum_mul, rw add_div, apply congr_arg2,
      { rw div_eq_iff _,
        { rw div_mul_comm', rw nsmul_eq_mul, apply congr_arg2,
          { norm_num, rw mul_div_mul_left _, rw pow_succ, rw mul_div_cancel _,
            { norm_cast, apply pow_ne_zero m (nat.prime.ne_zero (fact_iff.1 _)), assumption, },
            { norm_num, apply ne_of_gt, apply fact_iff.1, assumption, }, },
          { rw zmod.int_cast_cast,
            rw zmod.nat_cast_val, rw ←zmod.nat_cast_val (x : zmod (d * p^m.succ)),
            apply congr_arg, rw ←zmod.nat_cast_val x, rw val_coe_eq_val _ _ _,
            { apply imp m, },
            { rw mul_comm d (p^m), rw mul_comm d (p^m.succ), apply mul_lt_mul,
              any_goals { simp, },
              { apply pow_lt_pow _ (nat.lt_succ_self m), apply nat.prime.one_lt, apply fact_iff.1,
                assumption, },
              { apply fact_iff.1, assumption, }, }, }, },
        { norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp m.succ, }, },
      { rw int.cast_mul, rw mul_div_assoc,
        have : (((∑ (x : fin p), (x : ℤ)) : ℤ) : ℚ) = (p - 1) * (p : ℚ) / 2, sorry,
        rw this, rw nat.cast_mul, rw int.cast_mul,
        have one : ((p : ℚ) - 1) * (p : ℚ) / 2 * (1 / (p : ℚ)) = ((p : ℚ) - 1) / 2, sorry,
        convert one using 2, rw div_eq_div_iff _ _,
        { rw one_mul, rw zmod.int_cast_cast, rw int.cast_pow, rw zmod.int_cast_cast,
          rw pow_succ', rw nat.cast_mul, rw nat.cast_pow, rw mul_assoc, apply congr_arg2,
          { rw ←zmod.nat_cast_val _,
            { rw zmod.val_nat_cast, congr, apply nat.mod_eq_of_lt, rw lt_mul_iff_one_lt_right _,
              { rw ←pow_succ', apply one_lt_pow,
                { apply nat.prime.one_lt, apply fact_iff.1, assumption, },
                { simp, }, },
              { apply fact_iff.1, assumption, }, },
            { rw ←pow_succ', apply imp (m + 1), } },
          { apply congr_arg2,
            { apply congr_arg2,
              { rw ←zmod.nat_cast_val _,
                { rw zmod.val_nat_cast, congr, apply nat.mod_eq_of_lt,
                  rw ←mul_assoc,
                  rw lt_mul_iff_one_lt_left _,
                  { apply one_lt_mul,
                    { rw nat.succ_le_iff, apply fact_iff.1, assumption, },
                    { apply one_lt_pow,
                      { apply nat.prime.one_lt, apply fact_iff.1, assumption, },
                      { rw nat.succ_le_iff, assumption, }, }, },
                  { apply nat.prime.pos, apply fact_iff.1, assumption, }, },
                { rw ←pow_succ', apply imp (m + 1), }, },
              { refl, }, },
            { refl, }, }, },
        { rw ←nat.cast_mul, norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp _, },
        { norm_cast, apply ne_of_gt, apply nat.prime.pos, apply fact_iff.1, assumption, }, }, }, },
  { rintros y,
    simp only [equiv.symm_apply_apply, subtype.val_eq_coe, equiv.inv_fun_as_coe,
      zmod.nat_cast_val], },
end
#exit
lemma div_coe (m n : ℕ) (h : m ∣ n) (a : zmod m) : ((a : zmod n) : zmod m) = a :=
begin
  conv_rhs
  { rw ←@zmod.ring_hom_map_cast _ (zmod n) _
      (@zmod.cast_hom _ _ h (zmod m) _ (zmod.char_p m)) a, },
  rw zmod.cast_hom_apply,
end

lemma fract_eq_val (n : ℕ) [h : fact (0 < n)] (a : zmod n) : fract ((a : ℚ) / n) = (a.val : ℚ) / n :=
begin
  rw fract_eq_iff, split,
  { apply div_nonneg _ _,
    { exact (zmod.val a).cast_nonneg, },
    { exact nat.cast_nonneg n, }, },
  split,
  { rw div_lt_one,
    { norm_cast, apply zmod.val_lt, },
    { norm_cast, apply fact_iff.1, assumption, }, },
  { rw ←zmod.nat_cast_val, use 0, simp, },
end

lemma card_equi_class (m : ℕ) (x : zmod (d * p^m)) :
  finset.card (@finset.univ (equi_class p d m m.succ (lt_add_one m) x) _) = p :=
begin
  rw finset.card_univ,
  rw ←fintype.of_equiv_card (equi_iso_fin p d m x),
  convert fintype.card_fin p,
end

lemma is_unit_mul (hc : gcd c p = 1) (hc' : gcd c d = 1) :
  is_unit ((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))) :=
begin
  rw is_unit, refine ⟨(zmod.unit_of_coprime c _), _⟩,
  { apply nat.coprime.symm (nat.coprime.mul (nat.coprime.symm hc')
      (nat.coprime.pow_left m.succ (nat.coprime.symm hc))), },
  { rw zmod.coe_unit_of_coprime c _,
    rw zmod.cast_nat_cast _,
    swap, { refine zmod.char_p _, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, }, },
end

lemma is_unit_mul' (hc : gcd c p = 1) (hc' : gcd c d = 1) :
  is_unit ((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^m)) :=
begin
  rw is_unit, refine ⟨(zmod.unit_of_coprime c _), _⟩,
  { apply nat.coprime.symm (nat.coprime.mul (nat.coprime.symm hc')
      (nat.coprime.pow_left m (nat.coprime.symm hc))), },
  { rw zmod.coe_unit_of_coprime c _,
    rw zmod.cast_nat_cast _,
    swap, { refine zmod.char_p _, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, rw ←one_mul m,
      apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, }, },
end

--example (a b c : ℤ) (h : a = b) : c * a = c * b := congr_arg (has_mul.mul c) h

-- A lot of goals are recurring, maybe make them local instances / lemmas?
lemma coe_inv (m : ℕ) (hc : gcd c p = 1) (hc' : gcd c d = 1) :
  ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m))⁻¹ =
  ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m.succ)) : zmod (d * p^m)) :=
begin
  have : ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)) =
    (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)),
    { repeat { rw zmod.cast_nat_cast _, },
      any_goals { refine zmod.char_p _ },
      any_goals { apply mul_dvd_mul_left, },
      any_goals { apply pow_dvd_pow _, },
      { apply nat.le_succ, },
      { linarith, },
      { rw ←one_mul m, apply mul_le_mul, any_goals { linarith, },
        { rw one_mul, apply nat.le_succ, }, }, },
  convert_to (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))⁻¹ = _,
  { apply congr_arg, assumption, },
  { have g1 : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))
      * (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))⁻¹ = 1,
    { rw zmod.mul_inv_of_unit, rw ←this, apply is_unit_mul' p d m hc hc', },
    have g2 : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))
      * ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m.succ)) : zmod (d * p^m)) = 1,
    { rw ←zmod.cast_mul _,
      { rw ←zmod.cast_one _,
        { congr, rw zmod.mul_inv_of_unit, apply is_unit_mul p d m hc hc', },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
    rw ←g1 at g2,
    have g3 := congr_arg (has_mul.mul
      ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m)))) g2,
    rw [←mul_assoc, ←mul_assoc, zmod.inv_mul_of_unit _, one_mul, one_mul] at g3,
    { rw g3, },
    { rw ←this, apply is_unit_mul' p d m hc hc', }, },
end

lemma rep (m : ℕ) : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)) =
  ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)) :=
begin
  repeat { rw zmod.cast_nat_cast _, },
  any_goals { refine zmod.char_p _, },
  any_goals { apply mul_dvd_mul_left, apply pow_dvd_pow, },
  { rw ←one_mul m, apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, },
  { apply nat.le_succ, },
  { linarith, },
end

lemma E_c_sum_equi_class' [has_coe ℝ R] [0 < m] (x : zmod (d * p^m)) (hc : gcd c p = 1)
  (hc' : gcd c d = 1) :
  ∑ (y : equi_class p d m m.succ (lt_add_one m) x), (E_c p d hc m.succ y) = (E_c p d hc m x) :=
begin
  rw E_c, simp only,
  haveI imp : ∀ n : ℕ, fact (0 < d * p^n),
  { rintros n, rw fact_iff at *, apply mul_pos,
    { assumption, },
    { apply ((pow_pos (nat.prime.pos _)) n), assumption, }, },
  have : ∀ (n : ℕ) (x : zmod (d * p^n)), 0 ≤ (x.val : ℚ) / (d * p^n) ∧ (x.val : ℚ) / (d * p^n) < 1,
  { rintros n x,
    split,
    { norm_cast, refine div_nonneg _ _,
      all_goals { norm_cast, apply nat.zero_le _, }, },
    { rw div_lt_one,
      { norm_cast, apply @zmod.val_lt _ _, apply imp n, },
      { norm_cast,apply fact_iff.1 (imp n), }, }, },
  rw [finset.sum_add_distrib, finset.sum_sub_distrib, sum_fract, ←finset.mul_sum],
  convert_to ((x.val : ℚ) / (d * p ^ m) + (p - 1) / 2) - (c : ℚ) *
    ∑ (x_1 : (equi_class p d m m.succ (lt_add_one m)
      ( ((c : zmod (d * p^(2*m.succ)))⁻¹ : zmod (d * p^m)) * x))),
    fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) +
    (∑ (x : (equi_class p d m m.succ _ x)), ((c : ℚ) - 1) / 2) = _ - _ + _,
  { rw [add_right_cancel_iff, sub_right_inj], apply congr_arg,
    apply finset.sum_bij,
    swap 5,
    { rintros, constructor, swap,
      { exact ((c : zmod (d * p^(2*m.succ)))⁻¹ : zmod (d * p^m.succ)) * a, },
      { rw mem_equi_class,
        have := (mem_equi_class p d m m.succ _ x a).1 a.prop,
        conv_rhs { congr, skip, rw ←this, },
        rw zmod.cast_mul _,
        { congr, rw coe_inv p d m hc hc', },
        swap, { exact zmod.char_p (d * p^m), },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, }, },
    { simp, }, --squeeze_simp does not work!
    { rintros, rw fract_eq_fract, simp only [subtype.coe_mk],
      rw [div_sub_div_same, zmod.nat_cast_val], use 0, simp, },
    { simp, rintros a1 ha1 a2 ha2 h, rw is_unit.mul_right_inj at h, assumption,
      { rw is_unit_iff_exists_inv',
        refine ⟨((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))),
          zmod.mul_inv_of_unit _ (is_unit_mul p d m hc hc')⟩, }, },
    { simp, rintros a ha, rw mem_equi_class at *,
      use ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) * a,
      split,
      { rw [mem_equi_class, zmod.cast_mul _],
        { rw ha,
          --have rep : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)) =
            --((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)), sorry,
          -- if I remove the above line, the convert below does not work?
          rw ←mul_assoc, convert one_mul x, norm_cast,
          convert zmod.mul_inv_of_unit _ (is_unit_mul' p d m hc hc') using 2, rw rep, },
           -- using 1,
          --{ apply is_unit_mul' p d m hc hc', }, },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
      { rw [←mul_assoc, zmod.inv_mul_of_unit _ _],
        { rw one_mul a, },
        apply is_unit_mul p d m hc hc', }, }, },
  rw [sum_fract, fract_eq_self (this m x).1 (this m x).2, mul_add, finset.sum_const, card_equi_class],
  simp only [nsmul_eq_mul],
  rw [sub_add_eq_add_sub, sub_add_eq_add_sub, sub_add_eq_sub_sub, sub_right_comm], congr,
  { rw [add_assoc, add_sub_assoc], congr, linarith, },
  { rw [←nat.cast_pow, ←nat.cast_mul, ←fract_eq_val _ _], repeat { apply congr_arg, },
    apply congr_fun, repeat { apply congr_arg, }, apply congr_fun, repeat { apply congr_arg, },
    repeat { rw zmod.cast_nat_cast _, }, repeat { any_goals { refine zmod.char_p _, }, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, rw ←one_mul m,
      apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, },
    apply imp m, },
end
#exit

lemma E_c_sum_equi_class [has_coe ℝ R] (x : zmod (d * p^m)) (hc : gcd c p = 1) :
∑ (y : zmod (d * p ^ m.succ)) in (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a)) x,
  ((E_c p d hc m.succ y) : R) = (E_c p d hc m x) :=
begin
  rw E_c, simp,
  have : ∀ (n : ℕ) (x : zmod (d * p^n)), 0 ≤ (x.val : ℝ) / (d * p^n) ∧ (x.val : ℝ) / (d * p^n) < 1,
  { rintros n x, split, sorry, sorry, },
  conv_lhs { congr, skip, funext, rw [fract_eq_self ((this m.succ x).1) ((this m.succ x).2)], },
  rw [fract_eq_self ((this m x).1) ((this m x).2)],
  rw ←finset.sum_finset_coe,
  -- conv_lhs { congr, },
  have := set.coe_to_finset (equi_class p d m m.succ _ x), rw [this],
  rw fintype.sum_equiv (equi_iso_fin p d m x),
  rw [finset.sum_add_distrib],

  --conv_lhs { congr, skip, funext, rw fract_eq_self, skip,
  --{ apply_congr (this _ _).1, }, },
  sorry,
end
-- why does has_div exist for ℤ and ℕ!?
#exit

lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : set α} (h : ¬disjoint s t) :
  ∃ x, x ∈ s ∧ x ∈ t :=
begin
  contrapose h, push_neg at h, rw not_not, rw disjoint_iff, simp [h], ext, split,
  { intro h', rw set.mem_inter_iff at h', specialize h x h'.1, simp, apply h h'.2, },
  { simp, },
end

lemma inter_nonempty_of_not_disjoint' {α : Type*} {s t : finset α} [decidable_eq α] (h : ¬disjoint s t) : ∃ x, x ∈ s ∧ x ∈ t :=
begin
  suffices : finset.nonempty (s ⊓ t),
  cases this with x hx, use x,
  rw ←finset.mem_inter, convert hx,
  rw finset.inf_eq_inter,
  rw finset.nonempty_iff_ne_empty,
  contrapose h, push_neg at h, rw not_not,
  rw disjoint, simp, -- simp does not work without rw disjoint
  rw finset.subset_empty, rw h,
end

noncomputable def g (hc : gcd c p = 1) (hd : 0 < d) (f : locally_constant (zmod d × ℤ_[p]) R) :
  @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ),
    --have hpos : 0 < d * p^n := mul_pos hd (pow_pos (nat.prime.pos (fact_iff.1 _inst_3)) n),
    --by
       --letI : fintype (zmod (d * p^n)) := @zmod.fintype _ ⟨hpos⟩; exact
    ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos p d n)), f(a) • ((E_c p d hc n a) : R),
  is_eventually_const := ⟨classical.some (factor_F p d R f),
  begin
  simp, rintros m hm, -- why is the simp needed?
  set t := λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a) with ht,
  rw succ_eq_bUnion_equi_class,
  rw @finset.sum_bUnion _ _ _ _ _ _ (zmod' (d*p^m) (mul_prime_pow_pos p d m)) t _,
  { conv_lhs { apply_congr, skip, conv { apply_congr, skip, rw equi_class_eq p d R m f x x_1 H_1, },
    rw [←finset.mul_sum], rw [E_c_sum_equi_class p d R m x hc], }, },
  { rintros x hx y hy hxy, contrapose hxy, push_neg,
    obtain ⟨z, hz⟩ := inter_nonempty_of_not_disjoint' hxy,
    rw ht at hz, simp at hz, rw mem_equi_class p d m m.succ at hz,
    rw mem_equi_class p d m m.succ at hz, cases hz with h1 h2, rw h1 at h2,
    exact h2, }, end⟩, }

lemma g_def (hc : gcd c p = 1) (hd : 0 < d) (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) :
  (g p d R hc hd f).to_seq n = ∑ a in (finset.range (d * p^n)),f(a) • ((E_c p d hc n a) : R) := sorry

/-
def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }
-/
example (U : clopen_basis' p d) : clopen_sets (zmod d × ℤ_[p]) := U


lemma char_fn_clopen_basis' (U : clopen_basis' p d) :
  char_fn _ U.val (coe (classical.some (classical.some_spec U.prop))) = (1 : R) :=
sorry

example {α : Type*} (s : set α) : s = {x : α | x ∈ s} := by simp only [set.set_of_mem_eq]

-- lemma ideally_not_needed (x : clopen_sets (zmod d × ℤ_[p])) (h : x ∈ clopen_basis' p d) :
--   clopen_basis' p d := ⟨x, h⟩

example (a b : R) (h : a + b = a) : b = 0 := add_right_eq_self.mp (congr_fun (congr_arg has_add.add h) b)

--example : clopen_basis' p d = {x // x ∈ clopen_basis' p d}

--lemma blahs : has_lift_t (clopen_basis' p d) (clopen_sets (zmod d × ℤ_[p])) :=

--example (U : clopen_sets (zmod d × ℤ_[p])) (hU : U ∈ clopen_basis' p d) : clopen_basis' p d := ⟨U, hU⟩

instance : semilattice_sup ℕ := infer_instance

example (m : ℕ) : m = 1 :=
begin

end

-- set_option pp.proofs true

-- def G (f : locally_constant ℤ_[p] R) (a : ℤ_[p]) : ℕ := ⨅ n : ℕ, loc_const_const -- is this really needed?

-- lemma loc_const_comp (f : locally_constant ℤ_[p] R)

-- can hd be removed?
lemma bernoulli_measure_nonempty (hc : gcd c p = 1) [hd : ∀ n : ℕ, fact (0 < d * p^n)] :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ hc) :=
begin
  refine mem_nonempty _,
  have hd' : 0 < d, sorry,
  refine { to_fun := λ f, sequence_limit (g p d R hc _ f),
  map_add' := _,
  map_smul' := _ },
  { sorry, },
  { rintros,
    set n := (sequence_limit_index' (g p d R hc hd' (x + y))) ⊔ (sequence_limit_index' (g p d R hc hd' x))
      ⊔ (sequence_limit_index' (g p d R hc hd' y)) with hn,
    --rw sequence_limit_eq (g p d R hc (x + y)) n _,
    repeat { rw sequence_limit_eq (g p d R hc hd' _) n _, },
    { repeat { rw g_def p d R hc hd' _ n, }, simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add], rw ←finset.sum_add_distrib,
      apply finset.sum_congr, refl,
      rintros, rw add_mul, },
    { rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, left, apply le_refl, }, },
  { rintros m x,
    set n := (sequence_limit_index' (g p d R hc hd' x)) ⊔ (sequence_limit_index' (g p d R hc hd' (m • x)))
      with hn,
    repeat { rw sequence_limit_eq (g p d R hc hd' _) n _, },
    { repeat { rw g_def p d R hc hd' _ n, }, simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply], rw finset.mul_sum,
      apply finset.sum_congr, refl,
      rintros, rw mul_assoc, },
    { rw le_sup_iff, left, apply le_refl, },
    { rw le_sup_iff, right, apply le_refl, }, }, --there has to be a less repetitive way of doing this
    { rw bernoulli_measure, simp only [le_refl, algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add, linear_map.coe_mk, locally_constant.coe_smul,
  subtype.forall, le_sup_iff, set.mem_set_of_eq, pi.smul_apply, subtype.coe_mk, set.singleton_prod, subtype.val_eq_coe],
  intros n a,
--      set V : clopen_basis' p d := ⟨U, hU⟩ with hV,
      --set V :=  with hV,
--      have : U = V.val, rw hV, simp,
--      set n := classical.some U.prop with hn,
--      set a := classical.some (classical.some_spec U.prop) with ha,
--      set n' := classical.some (mem_clopen_basis' p d U hU) with hn,
--      set a' := classical.some (classical.some_spec (mem_clopen_basis' p d U hU)) with ha,
/-/      have h1 : classical.some (bernoulli_measure._proof_5 p d
  ⟨U, (iff.refl (U ∈ clopen_basis' p d)).mpr ((iff.refl (U ∈ clopen_basis' p d)).mpr hU)⟩) = n,
      rw hn,
  have h2 : classical.some (classical.some_spec (bernoulli_measure._proof_5 p d
  ⟨U, (iff.refl (U ∈ clopen_basis' p d)).mpr ((iff.refl (U ∈ clopen_basis' p d)).mpr hU)⟩)) = a,
      rw ha, rw h1,
      rw ←hn, rw ←ha,
      show _ = E_c p d hc n a, -/
--      change' _ = E_c p d hc n _,
      have hd' : 0 < d, sorry,
      rw sequence_limit_eq (g p d R hc hd' _) n _,
      { rw g_def p d R hc hd' _ n,
        rw finset.sum_eq_add_sum_diff_singleton, swap 3, exact a.val,
        swap, simp,
        have := @zmod.val_lt (d * p^(n)) (hd n) a,
        sorry,
        rw zmod.nat_cast_val a, rw zmod.nat_cast_val a,
--        convert_to _ = E_c p d hc n a,

        conv_lhs { congr, congr, rw char_fn_clopen_basis' p d R, },
        rw one_smul,
        --rw ha, rw hn,
--        rw add_right_eq_self,

        refine finset.sum_eq_single _ _ _, },
      sorry, },
end

noncomputable
def linear_map_from_span (η : S → N)
  (cond : ∀ (f : S →₀ R'), finsupp.total S M R' coe f = 0 → finsupp.total S N R' η f = 0) :
  submodule.span R' S →ₗ[R'] N :=
begin
  let F := finsupp.total S M R' coe,
  let K := F.ker,
  let e := linear_map.quot_ker_equiv_range F,
  let ee : F.range ≃ₗ[R'] submodule.span R' S :=
    linear_equiv.of_eq _ _ (finsupp.span_eq_range_total _ _).symm,
  refine linear_map.comp _ ee.symm.to_linear_map,
  refine linear_map.comp _ e.symm.to_linear_map,
  refine F.ker.liftq (finsupp.total S N R' η) _,
  apply cond,
end

abbreviation s : set (locally_constant (zmod d × ℤ_[p]) R) := set.image (char_fn (zmod d × ℤ_[p]))
  (clopen_basis' p d)

def clopen_char_fn_equiv : clopen_basis' p d ≃ s p d R := sorry

def equi_class (n m : ℕ) (h : n < m) (a : zmod (p^n)) :=
 {b : zmod (p^m) | (b : zmod (p^n)) = a}

instance (n m : ℕ) (h : n < m) (a : zmod (p^n)) : fintype (equi_class p n m h a) := sorry

--construct a map from `ℤ/dℤ × ℤ_p → clopen_basis' p d` ?
/-- For m > n, χ_(b,a,n) = ∑_{j, b_j = a mod p^n} χ_(b,b_j,m) -/
lemma sum_char_fn_dependent (m n : ℕ) (h : m > n) (a : zmod (p^n)) (b : zmod d) :
  @char_fn (zmod d × ℤ_[p]) _ _ _ _ R _ _ _ (⟨_,
    is_clopen_prod (is_clopen_singleton (b : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩) = ∑ x in set.to_finset (equi_class p n m h a),
  char_fn _ (⟨_,
    is_clopen_prod (is_clopen_singleton (b : zmod d)) (proj_lim_preimage_clopen p d n x) ⟩) :=
sorry

#print E_c

/-- For m > n, E_c(χ_(b,a,n)) = ∑_{j, b_j = a mod p^n} E_c(χ_(b,b_j,m)) -/
lemma sum_char_fn_dependent_Ec (m n : ℕ) (h : m > n) (a : zmod (p^n)) (b : zmod d) (hc : gcd c p = 1) :
  E_c p d hc n a = ∑ x in set.to_finset (equi_class p n m h a), E_c p d hc m x :=
sorry

lemma seems_useless (x : s p d R) : (x : locally_constant (zmod d × ℤ_[p]) R) =
  char_fn (zmod d × ℤ_[p]) ((clopen_char_fn_equiv p d R).inv_fun x) :=
begin
  sorry,
end

lemma guess (n : ℕ) : zmod (d * (p^n)) ≃+* zmod d × zmod (p^n) :=
begin
  sorry,
end

lemma clopen_char_fn (U : clopen_basis' p d) : char_fn (zmod d × ℤ_[p]) U =
  @char_fn (zmod d × ℤ_[p]) _ _ _ _ R _ _ _ (⟨_,
    is_clopen_prod (is_clopen_singleton (coe (classical.some (classical.some_spec U.prop)) : zmod d))
      (proj_lim_preimage_clopen p d (classical.some U.prop) (classical.some (classical.some_spec U.prop))) ⟩) := sorry

--lemma trial : locally_constant (zmod d × ℤ_[p]) R = submodule.span R (s p d R) := sorry

-- TODO Remove this lemma
lemma mem_nonempty {α : Type*} {s : set α} {x : α} (h : x ∈ s) : nonempty s := ⟨⟨x, h⟩⟩

lemma bernoulli_measure_nonempty (hc : gcd c p = 1) :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ hc) :=
begin
  refine mem_nonempty _,
  {
    --constructor, swap 3,
    suffices : submodule.span R (s p d R) →ₗ[R] R, sorry, -- why you no work
      refine linear_map_from_span R _ _ (s p d R) _ _,
      { intro χ,
        --have : ∃ U : (clopen_basis' p d), char_fn _ U.val = (χ : locally_constant (zmod d × ℤ_[p]) R),
        --construct a bijection between `clopen_basis' p d` and `char_fn`?
        --sorry,
        --set U := classical.some this with hU,
        set U := (clopen_char_fn_equiv p d R).inv_fun χ with hU,
        exact E_c p d hc (classical.some U.prop) (classical.some (classical.some_spec U.prop)), },
      rintros f h, -- f is a relation, taking v in s to a; h says that ∑ a_i v_i = 0, tpt ∑ a_i E_c(v_i) = 0
      --apply finsupp.induction_linear f,
      rw finsupp.total_apply at *,
      simp,
      convert_to ∑ l in finsupp.support f, f(l) * (E_c p d hc (classical.some
        ((clopen_char_fn_equiv p d R).inv_fun l).prop) (classical.some (classical.some_spec
          ((clopen_char_fn_equiv p d R).inv_fun l).prop))) = 0,
      { rw finsupp.sum_of_support_subset,
        swap 4, exact f.support,
        simp, simp,
        { rintros i hi, rw zero_mul, }, },
      set n := ⨆ (l : finsupp.support f), classical.some
        ((clopen_char_fn_equiv p d R).inv_fun l).prop + 1 with hn,
--      set n := ⨆ (l : finsupp.support f), ((clopen_char_fn_equiv p d R).inv_fun l) with hn,
      rw finsupp.sum_of_support_subset at h,
      swap 4, exact f.support,
      swap, simp, swap, simp,
      conv_lhs at h { apply_congr, skip, rw seems_useless p d R x,
        rw clopen_char_fn _,
        rw [sum_char_fn_dependent p d R n (classical.some
          ((clopen_char_fn_equiv p d R).inv_fun x).prop) _ (coe (classical.some (classical.some_spec
          ((clopen_char_fn_equiv p d R).inv_fun x).prop))) _], },

      /-apply finsupp.induction f, { simp, },
      { rintros χ a g hg nza rel_g_zero h, rw finsupp.total_apply at *,
        rw finsupp.sum_add_index at *,
        {  }, sorry, sorry, sorry, sorry, },-/

      rw finsupp.total_apply,
      apply submodule.span_induction (trial p d R f),
      set s := classical.some (what_to_do p d R f) with hs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set i := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R f))) with hi,
      set j := classical.some (classical.some_spec (what_to_do p d R f)) with hj,
      have hs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R f))),
      exact ∑ (k : s), (j k) •
      (E_c p d hc (classical.some (i k).prop) (classical.some (classical.some_spec (i k).prop))),
    { rintros f g,
      set fs := classical.some (what_to_do p d R f) with hfs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set fi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R f))) with hfi,
      set fj := classical.some (classical.some_spec (what_to_do p d R f)) with hfj,
      have hfs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R f))),
      set gs := classical.some (what_to_do p d R g) with hgs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set gi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R g))) with hgi,
      set gj := classical.some (classical.some_spec (what_to_do p d R g)) with hgj,
      have hgs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R g))),
      set fgs := classical.some (what_to_do p d R (f + g)) with hfgs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set fgi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R (f + g)))) with hfgi,
      set fgj := classical.some (classical.some_spec (what_to_do p d R (f + g))) with hfgj,
      have hfgs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R (f + g)))),
      convert_to ∑ (k : fgs), (fgj k) •
      (E_c p d hc (classical.some (fgi k).prop) (classical.some (classical.some_spec (fgi k).prop)) : R) =
      ∑ (k : fs), (fj k) •
      (E_c p d hc (classical.some (fi k).prop) (classical.some (classical.some_spec (fi k).prop)) : R) +
      ∑ (k : gs), (gj k) •
      (E_c p d hc (classical.some (gi k).prop) (classical.some (classical.some_spec (gi k).prop))),
  sorry, },
    sorry, },
sorry,
end

/-instance (c : ℤ) (hc : gcd c p = 1) : distribution' (ℤ_[p]) :=
{
  phi := (classical.choice (bernoulli_measure_nonempty p c hc)).val
} -/

/-lemma subspace_induces_locally_constant (U : set X) [hU : semimodule A (locally_constant ↥U A)]
  (f : locally_constant U A) :
  ∃ (g : locally_constant X A), f.to_fun = (set.restrict g.to_fun U) := sorry -/

example {A B C D : Type*} (f : A → B) (g : C → D) : A × C → B × D := by refine prod.map f g

lemma subspace_induces_locally_constant (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  ∃ (g : locally_constant (zmod d × ℤ_[p]) A),
    f.to_fun = g.to_fun ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
sorry
--generalize to units X
#print uniform_continuous_uniformly_extend
instance is_this_even_true : compact_space (units (zmod d) × units ℤ_[p]) := sorry
instance why_is_it_not_recognized : t2_space (units (zmod d) × units ℤ_[p]) := sorry
instance so_many_times : totally_disconnected_space (units (zmod d) × units ℤ_[p]) := sorry

noncomputable lemma bernoulli_measure_of_measure (hc : gcd c p = 1) :
  measures'' (units (zmod d) × units ℤ_[p]) R :=
begin
  constructor, swap,
  constructor,
  constructor, swap 3, rintros f,
  choose g hg using subspace_induces_locally_constant R p d f, --cases does not work as no prop
  exact (classical.choice (bernoulli_measure_nonempty p d R hc)).val g,
  { sorry, },
  { sorry, },
  { sorry, },
end
--function on clopen subsets of Z/dZ* x Z_p* or work in Z_p and restrict
--(i,a + p^nZ_p) (i,d) = 1

lemma cont_paLf : continuous (λ (a : (units (zmod d) × units ℤ_[p])),
  ((pri_dir_char_extend p d R) a) * (inj (teichmuller_character p (a.snd)))^(p - 2)
  * (w.to_fun a : R)) :=
sorry

def f : R := sorry

--h wont go in the system if you put it in [], is this independent of c?
noncomputable def p_adic_L_function [h : function.injective inj] (hc : gcd c p = 1) :=
 (f R) * (integral (units (zmod d) × units ℤ_[p]) R sorry (bernoulli_measure_of_measure p d R hc)
⟨(λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dir_char_extend p d R) a) *
  (inj (teichmuller_character p a.snd))^(p - 2) * (w.to_fun a : R)), cont_paLf p d R inj w ⟩)
--is it accurate to say that ω⁻¹ = ω^(p - 2)? I think so
