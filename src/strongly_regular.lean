/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import combinatorics.simple_graph.basic
import data.set.finite
import data.set
import data.nat.basic
/-!
# Strongly regular graphs

## Main definitions

* `G.is_SRG_with n k ℓ μ` (see `simple_graph.is_SRG_with`) is a structure for
  a `simple_graph` satisfying the following conditions:
  * The cardinality of the vertex set is `n`
  * `G` is a regular graph with degree `k`
  * The number of common neighbors between any two adjacent vertices in `G` is `ℓ`
  * The number of common neighbors between any two nonadjacent vertices in `G` is `μ`

## TODO
- Prove that the parameters of a strongly regular graph
  obey the relation `(n - k - 1) * μ = k * (k - ℓ - 1)`
- Prove that if `I` is the identity matrix and `J` is the all-one matrix,
  then the adj matrix `A` of SRG obeys relation `A^2 = kI + ℓA + μ(J - I - A)`
-/

open finset

universes u

namespace simple_graph
variables {V : Type u}
variables [fintype V] [decidable_eq V]
variables (G : simple_graph V) [decidable_rel G.adj]

/--
A graph is strongly regular with parameters `n k ℓ μ` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `ℓ` common neighbors
 * every pair of nonadjacent vertices has `μ` common neighbors
-/
structure is_SRG_with (n k ℓ μ : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(of_adj : ∀ (v w : V), G.adj v w → fintype.card (G.common_neighbors v w) = ℓ)
(of_not_adj : ∀ (v w : V), v ≠ w → ¬G.adj v w → fintype.card (G.common_neighbors v w) = μ)

variables {G} {n k ℓ μ : ℕ}

/-- Empty graphs are strongly regular. Note that `ℓ` can take any value
  for empty graphs, since there are no pairs of adjacent vertices. -/
-- we use bottom and top for empty and complete graph as we get some lattice-y structure
-- from doing so. you can look in the simple graphs file for help
lemma bot_strongly_regular :
  (⊥ : simple_graph V).is_SRG_with (fintype.card V) 0 ℓ 0 :=
{ card := rfl, -- it's just an easy rfl here
  regular :=
    begin
      exact simple_graph.bot_degree,
    end,
  of_adj :=
    begin
      intros v w,
      simp_rw [bot_adj, false_implies_iff],
    end,
  of_not_adj :=
    begin
      intros v w h,
      rwa [bot_adj, not_false_iff, true_implies_iff, fintype.card_eq_zero_iff, common_neighbors_eq, set.is_empty_coe_sort],
      apply set.inter_empty _,
    end }


/-- Complete graphs are strongly regular. Note that `μ` can take any value
  for complete graphs, since there are no distinct pairs of non-adjacent vertices. -/
lemma is_SRG_with.top :
  (⊤ : simple_graph V).is_SRG_with (fintype.card V) (fintype.card V - 1) (fintype.card V - 2) μ :=
{ card := rfl,
  regular := complete_graph_degree,
  of_adj :=
    begin
      intros v w h,
      rw card_common_neighbors_top h.ne,
    end,
  of_not_adj :=
    begin
      intros v w h c,
      contrapose c,
      rw top_adj,
      push_neg,
      exact h,
    end }

/-!
The unfortunate thing with talking about cardinalities of things like neighbor sets of vertices
is you'll run into finset or fintype issues where Lean isn't sure about the type equality of
certain things. This lemma is rather annoying to prove so if you want to skip it and just use it
as a sorry'd lemma, go right ahead! Otherwise, some useful lemmas in the proof include things like
* natural number cancellation lemmas
* set.to_finset lemmas
* finset.card lemmas
-/
lemma is_SRG_with.card_neighbor_finset_union_eq {v w : V} (h : G.is_SRG_with n k ℓ μ) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card =
    2 * k - fintype.card (G.common_neighbors v w) :=
begin
  rw eq_comm,
  rw nat.sub_eq_iff_eq_add,
  {
    unfold common_neighbors,
    rw ← set.to_finset_card,
    rw set.to_finset_inter,
    unfold neighbor_finset,
    rw finset.card_union_add_card_inter,
    rwa [set.to_finset_card, set.to_finset_card, card_neighbor_set_eq_degree, card_neighbor_set_eq_degree],
    have g: G.is_regular_of_degree k := is_SRG_with.regular h,
    rwa [g v, g w],
    exact two_mul k,
  },
  {
    calc
      fintype.card ↥(G.common_neighbors v w) ≤ G.degree v : card_common_neighbors_le_degree_left G _ _
                                          ...= k : is_SRG_with.regular h v
                                          ...≤ 2*k : nat.le_mul_of_pos_left (nat.succ_pos 1),
  }
end

/-- Assuming `G` is strongly regular, `2*(k + 1) - m` in `G` is the number of vertices that are
  adjacent to either `v` or `w` when `¬G.adj v w`. So it's the cardinality of
  `G.neighbor_set v ∪ G.neighbor_set w`. -/
-- hint: the last lemma is useful here!
lemma is_SRG_with.card_neighbor_finset_union_of_not_adj {v w : V} (h : G.is_SRG_with n k ℓ μ)
  (hne : v ≠ w) (ha : ¬G.adj v w) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card = 2 * k - μ :=
begin
  have g := is_SRG_with.of_not_adj h v w hne ha,
  rw ← g,
  exact h.card_neighbor_finset_union_eq,
end

lemma is_SRG_with.card_neighbor_finset_union_of_adj {v w : V} (h : G.is_SRG_with n k ℓ μ)
  (ha : G.adj v w) :
  (G.neighbor_finset v ∪ G.neighbor_finset w).card = 2 * k - ℓ :=
begin
  have g := h.of_adj v w ha,
  rw ← g,
  exact h.card_neighbor_finset_union_eq,
end

-- hint: ext is a useful command in this one! whenever you see two sets being equal as your goal,
-- talking about the elements is often a good place to start.
lemma compl_neighbor_finset_sdiff_inter_eq {v w : V} :
  (G.neighbor_finset v)ᶜ \ {v} ∩ ((G.neighbor_finset w)ᶜ \ {w}) =
    (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}) :=
begin
  ext,
  simp_rw [finset.mem_inter, finset.mem_sdiff, finset.mem_inter, finset.mem_union, push_neg.not_or_eq],
  cc,
end

/-!
Here we have a less tedious proof - this one just uses a lot of set theory lemmas but is otherwise
pretty straightforward.
-/
lemma sdiff_compl_neighbor_finset_inter_eq {v w : V} (h : G.adj v w) :
  (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ \ ({w} ∪ {v}) =
    (G.neighbor_finset v)ᶜ ∩ (G.neighbor_finset w)ᶜ :=
begin
  ext,
  split,
  {
    intro h,
    rw mem_sdiff at h,
    exact h.left,
  },
  {
    by_contra,
    push_neg at h,
    cases h with ha hb,
    rw mem_sdiff at hb,
    push_neg at hb,
    have g:=hb ha,
    rw mem_inter at ha,
    cases ha with hav haw,
    rw mem_union at g,
    cases g,
    {
      rw mem_singleton at g,
      rw [g, finset.mem_compl, simple_graph.mem_neighbor_finset G v w] at hav,
      apply absurd h hav, 
    },
    {
      rw mem_singleton at g,
      rw [g, finset.mem_compl, simple_graph.mem_neighbor_finset G w v] at haw,
      apply absurd (adj.symm h) haw,                             
    }
  }
end

lemma is_SRG_with.compl_is_regular (h : G.is_SRG_with n k ℓ μ) :
  Gᶜ.is_regular_of_degree (n - k - 1) :=
begin
  intro v,
  rw [degree_compl, h.regular, h.card, nat.sub.right_comm],
end

/-!
This one is more tedious, you can take it as sorry'd, although simp does a lot of the work if you
can set things up nicely
-/
lemma is_SRG_with.card_common_neighbors_eq_of_adj_compl (h : G.is_SRG_with n k ℓ μ)
  {v w : V} (ha : Gᶜ.adj v w) :
  fintype.card ↥(Gᶜ.common_neighbors v w) = n - (2 * k - μ) - 2 :=
begin
  unfold common_neighbors,
  rw ← h.card_neighbor_finset_union_of_not_adj ha.ne (ha.right),
  symmetry,
  rw [nat.sub.right_comm, nat.sub_eq_iff_eq_add],
  {
    rw [← set.to_finset_card, set.to_finset_inter, ← neighbor_finset, ← neighbor_finset, nat.add_comm],
    --rw [neighbor_finset_compl, neighbor_finset_compl],
    rw ← card_union_add_card_inter,
    rw finset.union_distrib_left,
    rw finset.union_comm,
    rw ← finset.union_assoc,
    --rw neighbor_set_union_compl_neighbor_set_eq,
    sorry,
  },
  {
    sorry,
  }
end

/-!
simp can do a lot of the heavy lifting here too, it's similarly tedious
-/
lemma is_SRG_with.card_common_neighbors_eq_of_not_adj_compl (h : G.is_SRG_with n k ℓ μ)
  {v w : V} (hn : v ≠ w) (hna : ¬Gᶜ.adj v w)  :
  fintype.card ↥(Gᶜ.common_neighbors v w) = n - (2 * k - ℓ) :=
begin
  sorry,
end

/-- The complement of a strongly regular graph is strongly regular. -/
lemma is_SRG_with.compl (h : G.is_SRG_with n k ℓ μ) :
  Gᶜ.is_SRG_with n (n - k - 1) (n - (2 * k - μ) - 2) (n - (2 * k - ℓ)) :=
{ card := h.card,
  regular :=
    begin
      exact h.compl_is_regular,
    end,
  of_adj :=
    begin
      intros v w,
      exact h.card_common_neighbors_eq_of_adj_compl,
    end,
  of_not_adj :=
    begin
      intros v w,
      exact h.card_common_neighbors_eq_of_not_adj_compl,
    end }

end simple_graph
