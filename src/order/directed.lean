/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.lattice
import data.set.basic

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `directed_on r s`: Predicate stating that the set `s` is `r`-directed.
* `is_directed α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes.
-/

open function

universes u v w

variables {α : Type u} {β : Type v} {ι : Sort w} (r s : α → α → Prop)
local infix ` ≼ ` : 50 := r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed (f : ι → α) := ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on (s : set α) := ∀ (x ∈ s) (y ∈ s), ∃ z ∈ s, x ≼ z ∧ y ≼ z

variables {r}

theorem directed_on_iff_directed {s} : @directed_on α r s ↔ directed r (coe : s → α) :=
by simp [directed, directed_on]; refine ball_congr (λ x hx, by simp; refl)

alias directed_on_iff_directed ↔ directed_on.directed_coe _

theorem directed_on_image {s} {f : β → α} :
  directed_on r (f '' s) ↔ directed_on (f ⁻¹'o r) s :=
by simp only [directed_on, set.ball_image_iff, set.bex_image_iff, order.preimage]

theorem directed_on.mono {s : set α} (h : directed_on r s)
  {r' : α → α → Prop} (H : ∀ {a b}, r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, zs, xz, yz⟩ := h x hx y hy in ⟨z, zs, H xz, H yz⟩

theorem directed_comp {ι} {f : ι → β} {g : β → α} :
  directed r (g ∘ f) ↔ directed (g ⁻¹'o r) f := iff.rfl

theorem directed.mono {s : α → α → Prop} {ι} {f : ι → α}
  (H : ∀ a b, r a b → s a b) (h : directed r f) : directed s f :=
λ a b, let ⟨c, h₁, h₂⟩ := h a b in ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
  (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y)) (hf : directed r f) :
  directed rb (g ∘ f) :=
directed_comp.2 $ hf.mono hg

/-- A monotone function on a sup-semilattice is directed. -/
lemma directed_of_sup [semilattice_sup α] {f : α → β} {r : β → β → Prop}
  (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : directed r f :=
λ a b, ⟨a ⊔ b, H le_sup_left, H le_sup_right⟩

lemma monotone.directed_le [semilattice_sup α] [preorder β] {f : α → β} :
  monotone f → directed (≤) f :=
directed_of_sup

/-- An antitone function on an inf-semilattice is directed. -/
lemma directed_of_inf [semilattice_inf α] {r : β → β → Prop} {f : α → β}
  (hf : ∀ a₁ a₂, a₁ ≤ a₂ → r (f a₂) (f a₁)) : directed r f :=
λ x y, ⟨x ⊓ y, hf _ _ inf_le_left, hf _ _ inf_le_right⟩

/-- `is_directed α r` states that for any elements `a`, `b` there exists an element `c` such that
`r a c` and `r b c`. -/
class is_directed (α : Type*) (r : α → α → Prop) : Prop :=
(directed (a b : α) : ∃ c, r a c ∧ r b c)

lemma directed_of (r : α → α → Prop) [is_directed α r] (a b : α) : ∃ c, r a c ∧ r b c :=
is_directed.directed _ _

lemma directed_id [is_directed α r] : directed r id := by convert directed_of r
lemma directed_id_iff_is_directed : directed r id ↔ is_directed α r := ⟨λ h, ⟨h⟩, @directed_id _ _⟩

@[priority 100]  -- see Note [lower instance priority]
instance is_total.to_is_directed [is_total α r] : is_directed α r :=
⟨λ a b, or.cases_on (total_of r a b) (λ h, ⟨b, h, refl _⟩) (λ h, ⟨a, refl _, h⟩)⟩

lemma is_directed_mono [is_directed α r] (h : ∀ ⦃a b⦄, r a b → s a b) : is_directed α s :=
⟨λ a b, let ⟨c, ha, hb⟩ := is_directed.directed a b in ⟨c, h ha, h hb⟩⟩

lemma exists_ge_ge [has_le α] [is_directed α (≤)] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
directed_of (≤) a b

lemma exists_le_le [has_le α] [is_directed α (swap (≤))] (a b : α) : ∃ c, c ≤ a ∧ c ≤ b :=
directed_of (swap (≤)) a b

instance order_dual.is_directed_ge [has_le α] [is_directed α (≤)] : is_directed α (swap (≤)) :=
‹is_directed α (≤)›

instance order_dual.is_directed_le [has_le α] [is_directed α (swap (≤))] : is_directed α (≤) :=
‹is_directed α (swap (≤))›

@[priority 100]  -- see Note [lower instance priority]
instance semilattice_sup.to_is_directed_le [semilattice_sup α] : is_directed α (≤) :=
⟨λ a b, ⟨a ⊔ b, le_sup_left, le_sup_right⟩⟩

@[priority 100]  -- see Note [lower instance priority]
instance semilattice_inf.to_is_directed_ge [semilattice_inf α] : is_directed α (swap (≤)) :=
⟨λ a b, ⟨a ⊓ b, inf_le_left, inf_le_right⟩⟩
