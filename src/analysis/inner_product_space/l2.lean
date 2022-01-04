/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.lp_space

/-!
# Identifications of a Hilbert space with `ℓ²`; Hilbert bases


-/

open is_R_or_C submodule filter
open_locale big_operators nnreal ennreal direct_sum

local attribute [instance] fact_one_le_two_ennreal

notation `ℓ²(` ι `,` 𝕜 `)` := lp (λ i : ι, 𝕜) 2

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E] [cplt : complete_space E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace orthogonal_family
variables {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V)
include hV

protected lemma summable_of_lp [complete_space E] (f : lp (λ i, V i) 2) :
  summable (λ i, (f i : E)) :=
begin
  rw hV.summable_iff_norm_sq_summable,
  convert (lp.mem_ℓp f).summable _,
  { norm_cast },
  { norm_num }
end

include cplt

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linear_isometry : lp (λ i, V i) 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, f i,
  map_add' := λ f g, by simp [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g)],
  map_smul' := λ c f, by simpa using tsum_const_smul (hV.summable_of_lp f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 ≤ (2:ℝ≥0∞).to_real := ennreal.to_real_nonneg,
    suffices : ∥∑' (i : ι), (f i : E)∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on (by norm_num) (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (lp.has_sum_norm (by norm_num) f),
    convert (hV.summable_of_lp f).has_sum.norm.rpow_const (or.inr H),
    ext s,
    exact_mod_cast (hV.norm_sum f s).symm,
  end }

protected lemma linear_isometry_apply (f : lp (λ i, V i) 2) :
  hV.linear_isometry f = ∑' i, f i :=
rfl

protected lemma has_sum_linear_isometry (f : lp (λ i, V i) 2) :
  has_sum (λ i, (f i : E)) (hV.linear_isometry f) :=
(hV.summable_of_lp f).has_sum

@[simp] protected lemma linear_isometry_apply_single [decidable_eq ι] {i : ι} {x : E} (hx : x ∈ V i) :
  hV.linear_isometry (dfinsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2) = x :=
begin
  let fx : lp (λ i, V i) 2 := dfinsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2,
  suffices : ∀ j ≠ i, (fx j : E) = 0, by simpa [foo_apply] using tsum_eq_single i this,
  intros j hj,
  have : fx j = 0 := dfinsupp.single_eq_of_ne hj.symm,
  simp [this],
end

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected lemma range_linear_isometry [Π i, complete_space (V i)] :
  hV.linear_isometry.to_linear_map.range = topological_closure (⨆ i, V i) :=
begin
  classical,
  refine le_antisymm _ _,
  { rintros x ⟨f, rfl⟩,
    refine mem_closure_of_tendsto (hV.has_sum_linear_isometry f) (eventually_of_forall _),
    intros s,
    refine sum_mem (supr V) _,
    intros i hi,
    exact mem_supr_of_mem i (f i).prop },
  { apply topological_closure_minimal,
    { refine supr_le _,
      intros i x hx,
      use dfinsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2,
      { simp, } },
    exact hV.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed }
end

end orthogonal_family

namespace orthonormal
variables {v : ι → E} (hv : orthonormal 𝕜 v)

include hv
protected lemma summable_of_lp [complete_space E] (f : ℓ²(ι, 𝕜)) :
  summable (λ i, f i • v i) :=
begin
  rw hv.summable_smul_iff_sq_summable,
  convert (lp.mem_ℓp f).summable _,
  { norm_cast },
  { norm_num }
end

include cplt

/-- An `ι`-indexed orthonormal set of vectors in `E` induce a linear isometry from `ℓ²(ι, 𝕜)` into
`E`. -/
protected def linear_isometry : ℓ²(ι, 𝕜) →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, f i • v i,
  map_add' := λ f g, by simp [tsum_add (hv.summable_of_lp f) (hv.summable_of_lp g), add_smul],
  map_smul' := λ c f, by simpa [mul_smul] using tsum_const_smul (hv.summable_of_lp f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 ≤ (2:ℝ≥0∞).to_real := ennreal.to_real_nonneg,
    suffices : ∥∑' (i : ι), f i • v i∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on (by norm_num) (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (lp.has_sum_norm (by norm_num) f),
    convert (hv.summable_of_lp f).has_sum.norm.rpow_const (or.inr H),
    ext s,
    suffices : ∑ i in s, ∥f i∥ ^ 2 = ∥∑ i in s, f i • v i∥ ^ 2,
    { exact_mod_cast this },
    sorry -- add this
  end }

protected lemma linear_isometry_apply (f : ℓ²(ι, 𝕜)) :
  hv.linear_isometry f = ∑' i, f i • v i :=
rfl

protected lemma has_sum_linear_isometry (f : ℓ²(ι, 𝕜)) :
  has_sum (λ i, f i • v i) (hv.linear_isometry f) :=
(hv.summable_of_lp f).has_sum

@[simp] protected lemma linear_isometry_apply_single [decidable_eq ι] (i : ι) (x : 𝕜) :
  hv.linear_isometry (finsupp.mk_lp (finsupp.single i x) 2) = x • v i :=
begin
  let fx : lp (λ i, V i) 2 := finsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2,
  suffices : ∀ j ≠ i, (fx j : E) = 0, by simpa [foo_apply] using tsum_eq_single i this,
  intros j hj,
  have : fx j = 0 := dfinsupp.single_eq_of_ne hj.symm,
  simp [this],
end

/-- The canonical linear isometry from the `lp 2` of  `ι → 𝕜`, induced by an `ι`-indexed orthonormal
set of vectors in `E`, has range the closure of the span of the vectors. -/
protected lemma range_linear_isometry :
  hv.linear_isometry.to_linear_map.range = (span 𝕜 (set.range v)).topological_closure :=
begin
  classical,
  refine le_antisymm _ _,
  { rintros x ⟨f, rfl⟩,
    refine mem_closure_of_tendsto (hv.has_sum_linear_isometry f) (eventually_of_forall _),
    intros s,
    refine sum_mem (span 𝕜 _) _,
    intros i hi,
    refine smul_mem _ _ _,
    refine subset_span _,
    exact set.mem_range_self i },
  { apply topological_closure_minimal,
    { rw span_le,
      rintros - ⟨i, rfl⟩,
      use dfinsupp.mk_lp (finsupp.single i 1) 2,
      { simp, } },
    exact hv.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed }
end

end orthonormal
