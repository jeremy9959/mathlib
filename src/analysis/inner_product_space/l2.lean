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

local attribute [instance] fact_one_le_two_ennreal

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

-- /-
--  If `ι` is a type and each space `f i`, `i : ι`, is an inner product space,
-- then the normed space `Lp f 2`, a subtype of `Π i, f i`, inherits a compatible inner product space
-- structure.
-- -/
-- instance lp.inner_product_space {ι : Type*} (f : ι → Type*)
--   [Π i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (lp f 2) :=
-- { inner := λ x y, ∑' i, inner (x i) (y i),
--   norm_sq_eq_inner := sorry,
--   conj_sym := sorry,
--   add_left := sorry,
--   smul_left := sorry }

-- @[simp] lemma lp.inner_apply {ι : Type*} {f : ι → Type*}
--   [Π i, inner_product_space 𝕜 (f i)] (x y : lp f 2) :
--   ⟪x, y⟫ = ∑' i, ⟪x i, y i⟫ :=
-- rfl

-- lemma lp.norm_eq_of_l2 {ι : Type*} {f : ι → Type*}
--   [Π i, inner_product_space 𝕜 (f i)] (x : lp f 2) :
--   ∥x∥ = sqrt (∑' (i : ι), ∥x i∥ ^ 2) :=
-- sorry

lemma baz' [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V)
  (f : lp (λ i, V i) 2) :
  summable (λ i, (f i : E)) :=
begin
  rw hV.summable_iff_norm_sq_summable,
  convert (lp.mem_ℓp f).summable _,
  { norm_cast },
  { norm_num }
end

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
def foo [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V) :
  lp (λ i, V i) 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, f i,
  map_add' := λ f g, by simp [tsum_add (baz' hV f) (baz' hV g)],
  map_smul' := λ c f, by simpa using tsum_const_smul (baz' hV f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 ≤ (2:ℝ≥0∞).to_real := ennreal.to_real_nonneg,
    suffices : ∥∑' (i : ι), (f i : E)∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on (by norm_num) (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (lp.has_sum_norm (by norm_num) f),
    convert (baz' hV f).has_sum.norm.rpow_const (or.inr H),
    ext s,
    exact_mod_cast (hV.norm_sum f s).symm,
  end }

lemma foo_apply [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V)
  (f : lp (λ i, V i) 2) :
  foo hV f = ∑' i, f i :=
rfl

lemma has_sum_foo [complete_space E] {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 V)
  (f : lp (λ i, V i) 2) :
  has_sum (λ i, (f i : E)) (foo hV f) :=
(baz' hV f).has_sum

@[simp] lemma foo_apply_single [decidable_eq ι] [complete_space E] {V : ι → submodule 𝕜 E}
  (hV : orthogonal_family 𝕜 V) {i : ι} {x : E} (hx : x ∈ V i) :
  foo hV (dfinsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2) = x :=
begin
  let fx : lp (λ i, V i) 2 := dfinsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2,
  suffices : ∀ j ≠ i, (fx j : E) = 0, by simpa [foo_apply] using tsum_eq_single i this,
  intros j hj,
  have : fx j = 0 := dfinsupp.single_eq_of_ne hj.symm,
  simp [this],
end

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
lemma range_foo [complete_space E] {V : ι → submodule 𝕜 E} [Π i, complete_space (V i)]
  (hV : orthogonal_family 𝕜 V) :
  (foo hV).to_linear_map.range = submodule.topological_closure (⨆ i, V i) :=
begin
  classical,
  refine le_antisymm _ _,
  { rintros x ⟨f, rfl⟩,
    refine mem_closure_of_tendsto (has_sum_foo hV f) (eventually_of_forall _),
    intros s,
    refine submodule.sum_mem (supr V) _,
    intros i hi,
    exact submodule.mem_supr_of_mem i (f i).prop },
  { apply submodule.topological_closure_minimal,
    refine supr_le _,
    intros i x hx,
    use dfinsupp.mk_lp (dfinsupp.single i ⟨x, hx⟩) 2,
    { simp, },
    exact (foo hV).isometry.uniform_inducing.is_complete_range.is_closed }
end

/-- A mutually orthogonal family of subspaces of `E`, whose span is dense in `E`, induce an
isometric equivalence from `E` to the `lp 2` of the subspaces. -/
def orthogonal_family.isometry_l2_of_dense_span
  [complete_space E] {V : ι → submodule 𝕜 E} [Π i, complete_space (V i)]
  (hV : orthogonal_family 𝕜 V) (hV' : submodule.topological_closure (⨆ i, V i) = ⊤) :
  E ≃ₗᵢ[𝕜] lp (λ i, V i) 2 :=
linear_isometry_equiv.symm $
linear_isometry_equiv.of_surjective (foo hV)
begin
  refine linear_map.range_eq_top.mp _,
  rw ← hV',
  exact range_foo hV,
end

@[simp] lemma orthogonal_family.isometry_l2_of_dense_span_symm_apply
  [complete_space E] {V : ι → submodule 𝕜 E} [Π i, complete_space (V i)]
  (hV : orthogonal_family 𝕜 V) (hV' : submodule.topological_closure (⨆ i, V i) = ⊤)
  (w : lp (λ i, V i) 2) :
  (hV.isometry_l2_of_dense_span hV').symm w = ∑' i, (w i : E) :=
foo_apply hV w

lemma orthogonal_family.has_sum_isometry_l2_of_dense_span_symm
  [complete_space E] {V : ι → submodule 𝕜 E} [Π i, complete_space (V i)]
  (hV : orthogonal_family 𝕜 V) (hV' : submodule.topological_closure (⨆ i, V i) = ⊤)
  (w : lp (λ i, V i) 2) :
  has_sum (λ i, (w i : E)) ((hV.isometry_l2_of_dense_span hV').symm w) :=
has_sum_foo hV w


/-- An orthonormal set of vectors in `E` indexed by `ι` induces a linear isometry from `lp 2` of
`ι → 𝕜` into `E`. -/
def foo' [complete_space E] {v : ι → E} (hv : orthonormal 𝕜 v) :
  lp (λ i : ι, 𝕜) 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, f i • v i,
  map_add' := sorry,
  map_smul' := sorry,
  norm_map' := sorry }

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ^2(ι, 𝕜)`. -/
structure hilbert_basis (ι : Type*) (𝕜 : Type*) [is_R_or_C 𝕜] (E : Type*) [inner_product_space 𝕜 E] :=
of_repr :: (repr : E ≃ₗᵢ[𝕜] (lp (λ i : ι, 𝕜) 2))

open submodule
variables {v : ι → E} (hli : orthonormal 𝕜 v)

lemma bzwz {v : ι → E} (hli : orthonormal 𝕜 v) : orthogonal_family 𝕜 (λ i, (𝕜 ∙ v i)) :=
begin
  intros i j hij,
  simp only [mem_span_singleton, forall_apply_eq_imp_iff', forall_exists_index],
  intros a b,
  simp [inner_smul_right, inner_smul_left, hli.2 hij],
end

include hli
/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected noncomputable def hilbert_basis.mk
  [complete_space E] (hsp : (span 𝕜 (range v)).topological_closure = ⊤) : hilbert_basis ι 𝕜 E :=
hilbert_basis.of_repr
begin
  haveI : ∀ i, complete_space (𝕜 ∙ v i) := sorry,
  refine (bzwz hli).isometry_l2_of_dense_span _,

end

protected noncomputable def hilbert_basis.mk_of_orthogonal_eq_bot
  [complete_space E] (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) : hilbert_basis ι 𝕜 E :=
hilbert_basis.mk hli
(by rw [← orthogonal_orthogonal_eq_closure, submodule.orthogonal_eq_top_iff, hsp])

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
lemma exists_hilbert_basis [complete_space E] {s : set E} (hs : orthonormal 𝕜 (coe : s → E)) :
∃ (w : set E), s ⊆ w ∧ nonempty (hilbert_basis w 𝕜 E) :=
let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs in
⟨ w,
  hws,
  ⟨ hilbert_basis.mk_of_orthogonal_eq_bot hw_ortho
    (by simpa [maximal_orthonormal_iff_orthogonal_complement_eq_bot hw_ortho] using hw_max) ⟩⟩
