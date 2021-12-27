/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.lp_space

/-!
# Hilbert (`L²`) sum of a (possibly infinite) family of inner product spaces


-/

open real set filter is_R_or_C
open_locale big_operators uniformity topological_space nnreal ennreal complex_conjugate direct_sum

lemma fact_one_le_two_ennreal : fact ((1:ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
local attribute [instance] fact_one_le_two_ennreal

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-
 If `ι` is a type and each space `f i`, `i : ι`, is an inner product space,
then the normed space `Lp f 2`, a subtype of `Π i, f i`, inherits a compatible inner product space
structure.
-/
instance Lp.inner_product_space {ι : Type*} (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (Lp f 2) :=
{ inner := λ x y, ∑' i, inner (x i) (y i),
  norm_sq_eq_inner := sorry,
  conj_sym := sorry,
  add_left := sorry,
  smul_left := sorry }

@[simp] lemma Lp.inner_apply {ι : Type*} {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x y : Lp f 2) :
  ⟪x, y⟫ = ∑' i, ⟪x i, y i⟫ :=
rfl

lemma Lp.norm_eq_of_L2 {ι : Type*} {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x : Lp f 2) :
  ∥x∥ = sqrt (∑' (i : ι), ∥x i∥ ^ 2) :=
sorry

lemma baz [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V)
  {f : Π i, V i} (hf : summable (λ i, ∥f i∥ ^ 2)) :
  summable (λ i, (f i : E)) :=
begin
  classical,
  rw summable_iff_cauchy_seq_finset at ⊢ hf,
  change _root_.cauchy _ at hf,
  change _root_.cauchy _,
  rw metric.cauchy_iff at ⊢ hf,
  refine ⟨filter.map_ne_bot, _⟩,
  intros ε hε,
  have hε' : 0 < (ε / 2) ^ 2 := sq_pos_of_pos (half_pos hε),
  obtain ⟨t, ht, H⟩ := hf.2 _ hε',
  simp at ht,
  obtain ⟨a, h⟩ := ht,
  refine ⟨_, image_mem_map (mem_at_top a), _⟩,
  rintros x y ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩,
  simp,
  have Hs₁ := H _ _ (h s₁ hs₁) (h a (finset.subset.refl _)),
  have Hs₂ := H _ _ (h s₂ hs₂) (h a (finset.subset.refl _)),
  rw dist_eq_norm at ⊢ Hs₁ Hs₂,
  rw real.norm_eq_abs at Hs₁ Hs₂,
  rw ← finset.sum_sdiff hs₁ at Hs₁ ⊢,
  rw ← finset.sum_sdiff hs₂ at Hs₂ ⊢,
  simp only [add_tsub_cancel_right] at Hs₁ Hs₂,
  rw _root_.abs_of_nonneg at Hs₁ Hs₂,
  calc _ = ∥∑ (x : ι) in s₁ \ a, (f x : E) - ∑ (x : ι) in s₂ \ a, (f x : E)∥ : by { congr' 1, abel }
  ... ≤ ∥∑ (x : ι) in s₁ \ a, (f x : E)∥ + ∥∑ (x : ι) in s₂ \ a, (f x : E)∥ : norm_sub_le _ _
  ... < ε/2 + ε/2 : add_lt_add _ _
  ... = ε : add_halves ε,
  -- nonnegativity and nice fact about finsets
  repeat { sorry }
end

lemma baz' [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V)
  (f : Lp (λ i, V i) 2) :
  summable (λ i, (f i : E)) :=
begin
  have : summable (λ (i : ι), ∥(f i : E)∥ ^ (2:ℝ≥0∞).to_real) := (Lp.mem_ℓp f).summable sorry,
  have : summable (λ (i : ι), ∥(f i : E)∥ ^ 2) := sorry,
  exact baz hV this,
end

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry
from `Lp 2` of the subspaces equipped with the `L2` inner product into `E`. -/
def foo [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V) :
  Lp (λ i, V i) 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, f i,
  map_add' := λ f g, by simp [tsum_add (baz' hV f) (baz' hV g)],
  map_smul' := λ c f, by simpa using tsum_const_smul (baz' hV f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 ≤ (2:ℝ≥0∞).to_real := ennreal.to_real_nonneg,
    suffices : ∥∑' (i : ι), (f i : E)∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on sorry (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (Lp.has_sum_norm sorry f),
    convert (baz' hV f).has_sum.norm.rpow_const (or.inr H),
    ext s,
    -- nice fact about finsets
    sorry
  end }

instance {E : ι → Type*} [Π i, normed_group (E i)] [Π i, complete_space (E i)] :
  complete_space (Lp E 2) :=
sorry

lemma is_closed_range_foo [complete_space E] {V : ι → submodule 𝕜 E} [Π i, complete_space (V i)]
  (hV : orthogonal_family 𝕜 V) :
  is_complete (set.range (foo hV)) :=
begin
  apply uniform_inducing.is_complete_range,
  convert (foo hV).isometry.uniform_inducing,
  -- rw complete_space_coe_iff_is_complete,
  -- have :=
  -- apply is_complete.is_closed
end

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
def direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.submodule_is_internal V)
  (hV' : orthogonal_family 𝕜 V) :
  E ≃ₗᵢ[𝕜] pi_Lp 2 (λ i, V i) :=
begin
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective _ hV.injective hV.surjective,
  refine (e₂.symm.trans e₁).isometry_of_inner _,
  suffices : ∀ v w, ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫,
  { intros v₀ w₀,
    convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀));
    simp only [linear_equiv.symm_apply_apply, linear_equiv.apply_symm_apply] },
  intros v w,
  transitivity ⟪(∑ i, (v i : E)), ∑ i, (w i : E)⟫,
  { simp [sum_inner, hV'.inner_right_fintype] },
  { congr; simp }
end

@[simp] lemma direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.submodule_is_internal V)
  (hV' : orthogonal_family 𝕜 V) (w : pi_Lp 2 (λ i, V i)) :
  (hV.isometry_L2_of_orthogonal_family hV').symm w = ∑ i, (w i : E) :=
begin
  classical,
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective _ hV.injective hV.surjective,
  suffices : ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i,
  { exact this (e₁.symm w) },
  intros v,
  simp [e₂, direct_sum.submodule_coe, direct_sum.to_module, dfinsupp.sum_add_hom_apply]
end
