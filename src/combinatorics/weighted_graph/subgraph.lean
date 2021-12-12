/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.weighted_graph.hom

/-!
# Subgraphs of a weighted graph

A subgraph of a weighted graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset. The edge subset is formalized as a
sub-relation of the adjacency relation of the weighted graph.

## Main definitions

* `G.subgraph` is the type of subgraphs of a `G : weighted_graph`

* `subgraph.neighbor_set`, `subgraph.incidence_set`, and `subgraph.degree` are like their
  `weighted_graph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `subgraph.coe` is the coercion from a `G' : G.subgraph` to a `weighted_graph G'.verts`.
  (This cannot be a `has_coe` instance since the destination type depends on `G'`.)

* `subgraph.is_spanning` for whether a subgraph is a spanning subgraph and
  `subgraph.is_induced` for whether a subgraph is an induced subgraph.

* Instances for `lattice (G.subgraph)` and `bounded_order (G.subgraph)`.

* `weighted_graph.to_subgraph`: If a `weighted_graph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `weighted_graph.subgraph` type.

* Graph homomorphisms from a subgraph to a graph (`subgraph.map_top`) and between subgraphs
  (`subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `set_like` does not apply to
  this kind of subobject.

## TODO

* Images of graph homomorphisms as subgraphs.

-/

variables {α W : Type*}

namespace weighted_graph

/-- A subgraph of a `weighted_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `α → α → Prop` as `set (α × α)`, a set of darts (i.e., half-edges), then
`subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure subgraph (G : weighted_graph α W) :=
(verts : set α)
(weight : α → α → option W)
(weight_comm (a b : α) : weight a b = weight b a)
(eq_of_weight_ne_none {a b : α} : weight a b ≠ none → weight a b = G.weight a b)
(mem_verts_of_weight_ne_none {a b : α} (h : weight a b ≠ none) : a ∈ verts)

namespace subgraph
variables {G : weighted_graph α W} (G' : G.subgraph)

@[simp] lemma weight_self (a : α) : G'.weight a a = none :=
begin
  classical,
  by_contra,
  exact h ((G'.eq_of_weight_ne_none h).trans $ G.weight_self a),
end

/-- Coercion from `G' : G.subgraph` to a `weighted_graph ↥G'.verts W`. -/
@[simps] def coe : weighted_graph G'.verts W :=
{ weight := λ a b, G'.weight a b,
  weight_self := λ a, G'.weight_self a,
  weight_comm := λ a b, G'.weight_comm a b }

/-- A subgraph is *spanning* if it contains all the vertices of `G`. --/
def is_spanning : Prop := ∀ a, a ∈ G'.verts

lemma is_spanning_iff {G' : G.subgraph} : G'.is_spanning ↔ G'.verts = set.univ :=
set.eq_univ_iff_forall.symm

/-- Coercion from `G.subgraph` to `weighted_graph α W`.  If `G'` is a spanning
subgraph, then `G'.spanning_coe` yields an isomorphic graph.
In general, this adds in all vertices from `α` as isolated vertices. -/
@[simps] def spanning_coe (G' : G.subgraph) : weighted_graph α W :=
{ weight := G'.weight,
  weight_self := G'.weight_self,
  weight_comm := G'.weight_comm }

/-- `spanning_coe` is equivalent to `coe` for a subgraph that `is_spanning`.  -/
@[simps] def spanning_coe_equiv_coe_of_spanning (G' : G.subgraph) (h : G'.is_spanning) :
  G'.spanning_coe ≃wg G'.coe :=
{ to_fun := λ v, ⟨v, h v⟩,
  inv_fun := λ v, v,
  left_inv := λ v, rfl,
  right_inv := λ ⟨v, hv⟩, rfl,
  weight_map' := λ a b, rfl }

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def is_induced (G' : G.subgraph) : Prop :=
∀ {a b : α}, a ∈ G'.verts → b ∈ G'.verts → G'.weight a b = G.weight a b

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def support (G' : G.subgraph) : set α := rel.dom (λ a b, G'.weight a b ≠ none)

lemma mem_support (G' : G.subgraph) {a : α} : a ∈ G'.support ↔ ∃ b, G'.weight a b ≠ none := iff.rfl

lemma support_subset_verts (G' : G.subgraph) : G'.support ⊆ G'.verts :=
λ a ⟨b, hb⟩, G'.mem_verts_of_weight_ne_none hb

/-- `G'.neighbor_set v` is the set of vertices adjacent to `v` in `G'`. -/
def neighbor_set (G' : G.subgraph) (a : α) : set α := set_of (λ b, G'.weight a b ≠ none)

lemma neighbor_set_subset (G' : G.subgraph) (a : α) : G'.neighbor_set a ⊆ G.neighbor_set a :=
λ w h, G'.adj_sub h

@[simp] lemma mem_neighbor_set (G' : G.subgraph) (a b : α) : w ∈ G'.neighbor_set v ↔ G'.adj a b :=
iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coe_neighbor_set_equiv {G' : G.subgraph} (v : G'.verts) :
  G'.coe.neighbor_set v ≃ G'.neighbor_set v :=
{ to_fun := λ w, ⟨w, by { obtain ⟨w', hw'⟩ := w, simpa using hw' }⟩,
  inv_fun := λ w, ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, by simpa using w.2⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def edge_set (G' : G.subgraph) : set (sym2 α) := sym2.from_rel G'.symm

lemma edge_set_subset (G' : G.subgraph) : G'.edge_set ⊆ G.edge_set :=
λ e, quotient.ind (λ e h, G'.adj_sub h) e

@[simp]
lemma mem_edge_set {G' : G.subgraph} {a b : α} : ⟦(v, w)⟧ ∈ G'.edge_set ↔ G'.adj a b := iff.rfl

lemma mem_verts_if_mem_edge {G' : G.subgraph} {e : sym2 α} {a : α}
  (he : e ∈ G'.edge_set) (hv : v ∈ e) : v ∈ G'.verts :=
begin
  refine quotient.ind (λ e he hv, _) e he hv,
  cases e with a b,
  simp only [mem_edge_set] at he,
  cases sym2.mem_iff.mp ha bith h h; subst h,
  { exact G'.edge_vert he, },
  { exact G'.edge_vert (G'.symm he), },
end

/-- The `incidence_set` is the set of edges incident to a given vertex. -/
def incidence_set (G' : G.subgraph) (a : α) : set (sym2 α) := {e ∈ G'.edge_set | v ∈ e}

lemma incidence_set_subset_incidence_set (G' : G.subgraph) (a : α) :
  G'.incidence_set v ⊆ G.incidence_set v :=
λ e h, ⟨G'.edge_set_subset h.1, h.2⟩

lemma incidence_set_subset (G' : G.subgraph) (a : α) : G'.incidence_set v ⊆ G'.edge_set :=
λ _ h, h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : G.subgraph) (a : α) (h : v ∈ G'.verts) : G'.verts := ⟨v, h⟩

/--
Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : G.subgraph)
  (α'' : set α) (hα : α'' = G'.verts)
  (adj' : α → α → Prop) (hadj : adj' = G'.adj) :
  G.subgraph :=
{ verts := α'',
  adj := adj',
  adj_sub := hadj.symm ▸ G'.adj_sub,
  edge_vert := hα.symm ▸ hadj.symm ▸ G'.edge_vert,
  symm := hadj.symm ▸ G'.symm }

lemma copy_eq (G' : G.subgraph)
  (α'' : set α) (hα : α'' = G'.verts)
  (adj' : α → α → Prop) (hadj : adj' = G'.adj) :
  G'.copy α'' hα adj' hadj = G' :=
subgraph.ext _ _ hα hadj

/-- The union of two subgraphs. -/
def union (x y : G.subgraph) : G.subgraph :=
{ verts := x.verts ∪ y.verts,
  adj := x.adj ⊔ y.adj,
  adj_sub := λ a b h, or.cases_on h (λ h, x.adj_sub h) (λ h, y.adj_sub h),
  edge_vert := λ a b h, or.cases_on h (λ h, or.inl (x.edge_vert h)) (λ h, or.inr (y.edge_vert h)),
  symm := λ a b h, by rwa [pi.sup_apply, pi.sup_apply, x.adj_comm, y.adj_comm] }

/-- The intersection of two subgraphs. -/
def inter (x y : G.subgraph) : G.subgraph :=
{ verts := x.verts ∩ y.verts,
  adj := x.adj ⊓ y.adj,
  adj_sub := λ a b h, x.adj_sub h.1,
  edge_vert := λ a b h, ⟨x.edge_vert h.1, y.edge_vert h.2⟩,
  symm := λ a b h, by rwa [pi.inf_apply, pi.inf_apply, x.adj_comm, y.adj_comm] }

/-- The `top` subgraph is `G` as a subgraph of itself. -/
def top : G.subgraph :=
{ verts := set.univ,
  adj := G.adj,
  adj_sub := λ a b h, h,
  edge_vert := λ a b h, set.mem_univ v,
  symm := G.symm }

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
def bot : G.subgraph :=
{ verts := ∅,
  adj := λ a b, false,
  adj_sub := λ a b h, false.rec _ h,
  edge_vert := λ a b h, false.rec _ h,
  symm := λ a b h, h }

instance subgraph_inhabited : inhabited (G.subgraph) := ⟨bot⟩

/-- The relation that one subgraph is a subgraph of another. -/
def is_subgraph (x y : G.subgraph) : Prop := x.verts ⊆ y.verts ∧ ∀ ⦃a b : α⦄, x.adj a b → y.adj a b

instance : lattice (G.subgraph) :=
{ le := is_subgraph,
  sup := union,
  inf := inter,
  le_refl := λ x, ⟨rfl.subset, λ _ _ h, h⟩,
  le_trans := λ x y z hxy hyz, ⟨hxy.1.trans hyz.1, λ _ _ h, hyz.2 (hxy.2 h)⟩,
  le_antisymm := begin
    intros x y hxy hyx,
    ext1 v,
    exact set.subset.antisymm hxy.1 hyx.1,
    ext a b,
    exact iff.intro (λ h, hxy.2 h) (λ h, hyx.2 h),
  end,
  sup_le := λ x y z hxy hyz,
            ⟨set.union_subset hxy.1 hyz.1,
              (λ a b h, h.cases_on (λ h, hxy.2 h) (λ h, hyz.2 h))⟩,
  le_sup_left := λ x y, ⟨set.subset_union_left x.verts y.verts, (λ a b h, or.inl h)⟩,
  le_sup_right := λ x y, ⟨set.subset_union_right x.verts y.verts, (λ a b h, or.inr h)⟩,
  le_inf := λ x y z hxy hyz, ⟨set.subset_inter hxy.1 hyz.1, (λ a b h, ⟨hxy.2 h, hyz.2 h⟩)⟩,
  inf_le_left := λ x y, ⟨set.inter_subset_left x.verts y.verts, (λ a b h, h.1)⟩,
  inf_le_right := λ x y, ⟨set.inter_subset_right x.verts y.verts, (λ a b h, h.2)⟩ }

instance : bounded_order (G.subgraph) :=
{ top := top,
  bot := bot,
  le_top := λ x, ⟨set.subset_univ _, (λ a b h, x.adj_sub h)⟩,
  bot_le := λ x, ⟨set.empty_subset _, (λ a b h, false.rec _ h)⟩ }

/-- Turn a subgraph of a `weighted_graph` into a member of its subgraph type. -/
@[simps] def _root_.weighted_graph.to_subgraph (H : weighted_graph α) (h : H ≤ G) :
  G.subgraph :=
{ verts := set.univ,
  adj := H.adj,
  adj_sub := h,
  edge_vert := λ a b h, set.mem_univ v,
  symm := H.symm }

lemma support_mono {H H' : G.subgraph} (h : H ≤ H') : H.support ⊆ H'.support :=
rel.dom_mono h.2

lemma _root_.weighted_graph.to_subgraph.is_spanning (H : weighted_graph α) (h : H ≤ G) :
  (H.to_subgraph h).is_spanning := set.mem_univ

lemma spanning_coe.is_subgraph_of_is_subgraph {H H' : G.subgraph} (h : H ≤ H') :
  H.spanning_coe ≤ H'.spanning_coe := h.2

/-- The top of the `G.subgraph` lattice is equivalent to the graph itself. -/
def top_equiv : (⊤ : G.subgraph).coe ≃g G :=
{ to_fun := λ v, ↑v,
  inv_fun := λ v, ⟨v, trivial⟩,
  left_inv := λ ⟨v, _⟩, rfl,
  right_inv := λ v, rfl,
  map_rel_iff' := λ a b, iff.rfl }

/-- The bottom of the `G.subgraph` lattice is equivalent to the empty graph on the empty
vertex type. -/
def bot_equiv : (⊥ : G.subgraph).coe ≃g (⊥ : weighted_graph empty) :=
{ to_fun := λ v, v.property.elim,
  inv_fun := λ v, v.elim,
  left_inv := λ ⟨_, h⟩, h.elim,
  right_inv := λ v, v.elim,
  map_rel_iff' := λ a b, iff.rfl }

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
def map {x y : G.subgraph} (h : x ≤ y) : x.coe →g y.coe :=
{ to_fun := λ v, ⟨↑v, and.left h v.property⟩,
  map_rel' := λ a b hvw, h.2 hvw }

lemma map.injective {x y : G.subgraph} (h : x ≤ y) : function.injective (map h) :=
λ a b h, by { simp only [map, rel_hom.coe_fn_mk, subtype.mk_eq_mk] at h, exact subtype.ext h }

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
def map_top (x : G.subgraph) : x.coe →g G :=
{ to_fun := λ v, v,
  map_rel' := λ a b hvw, x.adj_sub hvw }

lemma map_top.injective {x : G.subgraph} : function.injective x.map_top :=
λ a b h, subtype.ext h

@[simp]
lemma map_top_to_fun {x : G.subgraph} (v : x.verts) : x.map_top v = v := rfl

lemma neighbor_set_subset_of_subgraph {x y : G.subgraph} (h : x ≤ y) (a : α) :
  x.neighbor_set v ⊆ y.neighbor_set v :=
λ w h', h.2 h'

instance neighbor_set.decidable_pred (G' : G.subgraph) [h : decidable_rel G'.adj] (a : α) :
  decidable_pred (∈ G'.neighbor_set v) := h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finite_at {G' : G.subgraph} (v : G'.verts) [decidable_rel G'.adj]
   [fintype (G.neighbor_set v)] : fintype (G'.neighbor_set v) :=
set.fintype_subset (G.neighbor_set v) (G'.neighbor_set_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finite_at_of_subgraph {G' G'' : G.subgraph} [decidable_rel G'.adj]
   (h : G' ≤ G'') (v : G'.verts) [hf : fintype (G''.neighbor_set v)] :
   fintype (G'.neighbor_set v) :=
set.fintype_subset (G''.neighbor_set v) (neighbor_set_subset_of_subgraph h v)

instance coe_finite_at {G' : G.subgraph} (v : G'.verts) [fintype (G'.neighbor_set v)] :
  fintype (G'.coe.neighbor_set v) :=
fintype.of_equiv _ (coe_neighbor_set_equiv v).symm

/-- The degree of a vertex in a subgraph.  Is zero for vertices outside the subgraph. -/
def degree (G' : G.subgraph) (a : α) [fintype (G'.neighbor_set v)] : ℕ :=
fintype.card (G'.neighbor_set v)

lemma degree_le (G' : G.subgraph) (a : α)
  [fintype (G'.neighbor_set v)] [fintype (G.neighbor_set v)] :
  G'.degree v ≤ G.degree v :=
begin
  rw ←card_neighbor_set_eq_degree,
  exact set.card_le_of_subset (G'.neighbor_set_subset v),
end

lemma degree_le' (G' G'' : G.subgraph) (h : G' ≤ G'') (a : α)
  [fintype (G'.neighbor_set v)] [fintype (G''.neighbor_set v)] :
  G'.degree v ≤ G''.degree v :=
set.card_le_of_subset (neighbor_set_subset_of_subgraph h v)

@[simp] lemma coe_degree (G' : G.subgraph) (v : G'.verts)
  [fintype (G'.coe.neighbor_set v)] [fintype (G'.neighbor_set v)] :
  G'.coe.degree v = G'.degree v :=
begin
  rw ←card_neighbor_set_eq_degree,
  exact fintype.card_congr (coe_neighbor_set_equiv v),
end

end subgraph

end weighted_graph
