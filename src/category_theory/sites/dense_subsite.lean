/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.sites.sheaf

/-!
# Dense subsites

We define `cover_dense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

We will primarily consider cover-dense functors that are also full, since this notion is in general
not well-behaved otherwise. Note that https://ncatlab.org/nlab/show/dense+sub-site indeed has a
weaker notion of cover-dense that loosen this requirement, but it would not have all the properties
we would need, and some sheafification would be needed for here and there.

## Main results

- `category_theory.cover_dense.sheaf_hom`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any presheaf `ℱ` and sheaf `ℱ'` on `D`, and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`,
  we may glue them together to obtain a morphsim of sheaves `ℱ ⟶ ℱ'`.
- `category_theory.cover_dense.sheaf_iso`: If the `α` above is iso, then the result is also iso.
- `category_theory.cover_dense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`, then `α` is an iso if
  `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

universes v

namespace category_theory

variables {C : Type*} [category C] {D : Type*} [category D] {E : Type*} [category E]
variables (J : grothendieck_topology C) (K : grothendieck_topology D)
variables {L : grothendieck_topology E}

/--
Given a functor `G`, the presieve of `U : D` such that each arrows factors through images of `G`.
-/
def presieve.cover_by_image (G : C ⥤ D) (U : D) : presieve U :=
λ Y f, ∃ (Z : C) (f₁ : Y ⟶ G.obj Z) (f₂ : G.obj Z ⟶ U), f = f₁ ≫ f₂

/--
An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
@[nolint has_inhabited_instance]
structure presieve.cover_by_image_structure (G : C ⥤ D) {V U : D} (f : V ⟶ U) :=
(obj : C) (lift : V ⟶ G.obj obj) (map : G.obj obj ⟶ U) (fac' : f = lift ≫ map)

@[simp, reassoc]
lemma presieve.cover_by_image_structure.fac {G : C ⥤ D} {V U : D} {f : V ⟶ U}
  (h : presieve.cover_by_image_structure G f) : h.lift ≫ h.map = f := h.fac'.symm

/-- Obtain the auxiliary structure given `f ∈ cover_by_image G U`. -/
noncomputable
def presieve.get_cover_by_image_structure {G : C ⥤ D} {V U : D} {f : V ⟶ U}
  (hf : presieve.cover_by_image G U f) : presieve.cover_by_image_structure G f :=
begin
  choose a b c d using hf,
  exact ⟨a, b, c, d⟩,
end

/--
Given a functor `G`, the sieve of `U : D` such that each arrow factors through images of `G`.
-/
def sieve.cover_by_image (G : C ⥤ D) (U : D) : sieve U :=
⟨presieve.cover_by_image G U,
  λ X Y f ⟨Z, f₁, f₂, eq⟩ g, ⟨Z, g ≫ f₁, f₂, by rw [category.assoc, ←eq] ⟩⟩

lemma presieve.in_cover_by_image (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
  presieve.cover_by_image G X f := ⟨Y, 𝟙 _, f, by simp⟩

/--
A functor `G : (C, J) ⥤ (D, K)` is called `cover_dense` if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
structure cover_dense (K : grothendieck_topology D) (G : C ⥤ D) : Prop :=
(is_cover : ∀ (U : D), sieve.cover_by_image G U ∈ K U)

open presieve opposite
namespace cover_dense
variables {A : Type*} [category A] {K} {G : C ⥤ D} (H : cover_dense K G)

lemma ext (H : cover_dense K G) (ℱ : SheafOfTypes K) (X : D) {s t : ℱ.val.obj (op X)}
  (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) :
  s = t :=
begin
  apply (ℱ.property (sieve.cover_by_image G X) (H.is_cover X)).is_separated_for.ext,
  rintros Y _ ⟨Z, f₁, f₂, rfl⟩,
  simp[h f₂]
end

lemma functor_pullback_pushforward_covering [full G] (H : cover_dense K G) {X : C}
  (T : K (G.obj X)) : (T.val.functor_pullback G).functor_pushforward G ∈ K (G.obj X) :=
begin
  refine K.superset_covering _ (K.bind_covering T.property (λ Y f Hf, H.is_cover Y)),
  rintros Y _ ⟨Z, _, f, hf, ⟨W, g, f', rfl⟩, rfl⟩,
  use W, use G.preimage (f' ≫ f), use g,
  split,
  simpa using T.val.downward_closed hf f',
  simp,
end

/--
(Implementation). Given an hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps] def hom_over {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X : A) :
  G.op ⋙ (ℱ ⋙ coyoneda.obj (op X)) ⟶ G.op ⋙ (sheaf_over ℱ' X).val :=
whisker_right α (coyoneda.obj (op X))

/--
(Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps] def iso_over {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
  G.op ⋙ (sheaf_over ℱ X).val ≅ G.op ⋙ (sheaf_over ℱ' X).val :=
iso_whisker_right α (coyoneda.obj (op X))


lemma sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : sieve U} (hT)
  (x : family_of_elements _ T) (hx) (t) (h : x.is_amalgamation t) :
  t = (ℱ.property X T hT).amalgamate x hx :=
    (ℱ.property X T hT).is_separated_for x t _ h ((ℱ.property X T hT).is_amalgamation hx)


include H
variable [full G]
namespace types
variables {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : SheafOfTypes.{v} K} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
@[simp, nolint unused_arguments] noncomputable
def pushforward_family {X} (x : ℱ.obj (op X)) :
  family_of_elements ℱ'.val (cover_by_image G X) := λ Y f hf,
ℱ'.val.map (presieve.get_cover_by_image_structure hf).lift.op $ α.app (op _) $
  (ℱ.map (presieve.get_cover_by_image_structure hf).map.op x : _)

/-- (Implementation). The `pushforward_family` defined is compatible. -/
lemma pushforward_family_compatible {X} (x : ℱ.obj (op X)) :
  (pushforward_family H α x).compatible :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e,
  apply H.ext,
  intros Y f,
  simp only [pushforward_family, ←functor_to_types.map_comp_apply, ←op_comp],
  change (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _ =
    (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _,
  rw ← G.image_preimage (f ≫ g₁ ≫ _),
  rw ← G.image_preimage (f ≫ g₂ ≫ _),
  erw ← α.naturality (G.preimage _).op,
  erw ← α.naturality (G.preimage _).op,
  refine congr_fun _ x,
  simp only [quiver.hom.unop_op, functor.comp_map, ←op_comp, ←category.assoc,
    functor.op_map, ←ℱ.map_comp, G.image_preimage],
  congr' 3,
  simp[e]
end

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by glueing the `pushforward_family`. -/
noncomputable
def app_hom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := λ x,
  (ℱ'.property _ (H.is_cover X)).amalgamate
    (pushforward_family H α x)
    (pushforward_family_compatible H α x)

@[simp] lemma pushforward_family_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
  pushforward_family H α x f (presieve.in_cover_by_image G f) = α.app (op Y) (ℱ.map f.op x) :=
begin
  unfold pushforward_family,
  refine congr_fun _ x,
  rw ←G.image_preimage (get_cover_by_image_structure _).lift,
  change ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ = ℱ.map f.op ≫ α.app (op Y),
  erw ←α.naturality (G.preimage (get_cover_by_image_structure _).lift).op,
  simp only [←functor.map_comp, ←category.assoc, functor.comp_map, G.image_preimage,
     G.op_map, quiver.hom.unop_op, ←op_comp, presieve.cover_by_image_structure.fac],
end

@[simp] lemma app_hom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
  ℱ'.val.map f (app_hom H α X x) = α.app (op Y) (ℱ.map f x) :=
begin
  refine ((ℱ'.property _ (H.is_cover X)).valid_glue
    (pushforward_family_compatible H α x) f.unop (presieve.in_cover_by_image G f.unop)).trans _,
  apply pushforward_family_apply
end

@[simp] lemma app_hom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
  app_hom H α X ≫ ℱ'.val.map f = ℱ.map f ≫ α.app (op Y) :=
by { ext, apply app_hom_restrict }

/--
(Implementation). The maps given in `app_iso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps] noncomputable
def app_iso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : D) :
  ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X) :=
{ hom := app_hom H i.hom X,
  inv := app_hom H i.inv X,
  hom_inv_id' :=
  begin
    ext x,
    apply H.ext,
    intros Y f,
    simp
  end,
  inv_hom_id' :=
  begin
    ext x,
    apply H.ext,
    intros Y f,
    simp
  end }

/--
Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
-/
@[simps] noncomputable
def sheaf_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
{ app := λ X, app_hom H α (unop X), naturality' := λ X Y f,
  begin
    ext x,
    apply H.ext ℱ' (unop Y),
    intros Y' f',
    simp only [app_hom_restrict, types_comp_apply, ←functor_to_types.map_comp_apply],
    rw app_hom_restrict H α (f ≫ f'.op : op (unop X) ⟶ _)
  end }

/--
Given an natural isomorphsim `G ⋙ ℱ ≅ G ⋙ ℱ'` between sheaves of types, where `G` is full and
cover-dense, we may obtain a natural isomorphism between sheaves.
-/
@[simps] noncomputable
def sheaf_iso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ.val ≅ ℱ'.val :=
nat_iso.of_components (λ X, app_iso H i (unop X)) (sheaf_hom H i.hom).naturality

end types
open types

variables {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps] noncomputable
def sheaf_coyoneda_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  coyoneda ⋙ (whiskering_left Dᵒᵖ A Type*).obj ℱ ⟶
  coyoneda ⋙ (whiskering_left Dᵒᵖ A Type*).obj ℱ'.val :=
{ app := λ X, sheaf_hom H (hom_over α (unop X)), naturality' := λ X Y f,
  begin
  ext U x,
  change app_hom H (hom_over α (unop Y)) (unop U) (f.unop ≫ x) =
    f.unop ≫ app_hom H (hom_over α (unop X)) (unop U) x,
  symmetry,
  apply sheaf_eq_amalgamation,
  apply H.is_cover,
  intros Y' f' hf',
  change unop X ⟶ ℱ.obj (op (unop _)) at x,
  simp only [pushforward_family, functor.comp_map, coyoneda_obj_map, hom_over_app, category.assoc],
  congr' 1,
  conv_lhs { rw ←presieve.cover_by_image_structure.fac (get_cover_by_image_structure hf') },
  simp only [←category.assoc, op_comp, functor.map_comp],
  congr' 1,
  refine (app_hom_restrict H (hom_over α (unop X))
    (get_cover_by_image_structure hf').map.op x).trans _,
  simp
  end }

/--
(Implementation). `sheaf_coyoneda_hom` but the order of the arguments of the functor are swapped.
-/
@[simps] noncomputable
def sheaf_yoneda_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda :=
begin
  let α := sheaf_coyoneda_hom H α,
  refine { app := _, naturality' := _ },
  { intro U,
    refine { app := λ X, (α.app X).app U,
      naturality' := λ X Y f, by simpa using congr_app (α.naturality f) U } },
  { intros U V i,
    ext X x,
    exact congr_fun ((α.app X).naturality i) x },
end

/--
Given an natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between sheaves.
-/
@[simps] noncomputable
def sheaf_hom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  ℱ ⟶ ℱ'.val :=
begin
  have α' := sheaf_yoneda_hom H α,
  exact { app := λ X, yoneda.preimage (α'.app X),
          naturality' := λ X Y f, yoneda.map_injective (by simpa using α'.naturality f) }
end

/--
Given an natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between sheaves of arbitrary category,
where `G` is full and cover-dense, we may obtain a natural isomorphism between sheaves.
-/
@[simps] noncomputable
def sheaf_iso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
  ℱ.val ≅ ℱ'.val :=
begin
  haveI : ∀ (X : Dᵒᵖ), is_iso ((sheaf_hom H i.hom).app X),
  { intro X,
    apply is_iso_of_reflects_iso _ yoneda,
    use (sheaf_yoneda_hom H i.inv).app X,
    split;
      ext x : 2;
      simp only [sheaf_hom_app, nat_trans.comp_app, nat_trans.id_app, functor.image_preimage],
      exact ((sheaf_iso H (iso_over i (unop x))).app X).hom_inv_id,
      exact ((sheaf_iso H (iso_over i (unop x))).app X).inv_hom_id,
    apply_instance },
  haveI : is_iso (sheaf_hom H i.hom) := by apply nat_iso.is_iso_of_is_iso_app,
apply as_iso (sheaf_hom H i.hom),
end

/--
The constructed `sheaf_hom α` is equal to `α` when restricted onto `C`.
-/
lemma sheaf_hom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
  whisker_left G.op (sheaf_hom H α) = α :=
begin
  ext X,
  apply yoneda.map_injective,
  ext U,
  erw yoneda.image_preimage,
  symmetry,
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))), from _) = _,
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _),
  intros Y f hf,
  conv_lhs { rw ←presieve.cover_by_image_structure.fac (get_cover_by_image_structure hf) },
  simp only [pushforward_family, functor.comp_map, yoneda_map_app,
    coyoneda_obj_map, op_comp, functor_to_types.map_comp_apply, hom_over_app, ←category.assoc],
  congr' 1,
  simp only [category.assoc],
  congr' 1,
  rw ← G.image_preimage (get_cover_by_image_structure hf).map,
  symmetry,
  apply α.naturality (G.preimage (get_cover_by_image_structure hf).map).op,
  apply_instance
end

/--
If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
lemma sheaf_hom_eq (α : ℱ ⟶ ℱ'.val) :
  sheaf_hom H (whisker_left G.op α) = α :=
begin
  ext X,
  apply yoneda.map_injective,
  ext U,
  erw yoneda.image_preimage,
  symmetry,
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)), from _) = _,
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _),
  intros Y f hf,
  conv_lhs { rw ←presieve.cover_by_image_structure.fac (get_cover_by_image_structure hf) },
  simp [-presieve.cover_by_image_structure.fac],
  erw α.naturality_assoc,
  refl,
  apply_instance
end

/--
A full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable
def restrict_hom_equiv_hom :
  (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) :=
{ to_fun := sheaf_hom H,
  inv_fun := whisker_left G.op,
  left_inv := sheaf_hom_restrict_eq H,
  right_inv := sheaf_hom_eq H }

/--
Given a full and cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
lemma iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ.val ⟶ ℱ'.val)
  (i : is_iso (whisker_left G.op α)) : is_iso α :=
begin
  convert is_iso.of_iso (sheaf_iso H (as_iso (whisker_left G.op α))),
  symmetry,
  apply sheaf_hom_eq
end

end cover_dense

end category_theory
