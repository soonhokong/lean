/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Interactions between finset and set.
-/
import data.finset.comb data.set.function
open nat eq.ops set

namespace finset

variable {A : Type}
variable [deceq : decidable_eq A]
include deceq

definition to_set (s : finset A) : set A := λx, x ∈ s
abbreviation ts := @to_set A _  -- until coercion is working

variables (s t : finset A) (x : A)

/- operations -/

theorem mem_to_set_empty : (x ∈ ts ∅) = (x ∈ ∅) := rfl
theorem to_set_empty : ts ∅ = (∅ : set A) := rfl

theorem mem_to_set_univ [h : fintype A] : (x ∈ ts univ) = (x ∈ set.univ) :=
  propext (iff.intro (assume H, trivial) (assume H, !mem_univ))
theorem to_set_univ [h : fintype A] : ts univ = (set.univ : set A) := funext (λ x, !mem_to_set_univ)

theorem mem_to_set_union : (x ∈ ts (s ∪ t)) = (x ∈ ts s ∪ ts t) := !finset.mem_union_eq
theorem to_set_union : ts (s ∪ t) = ts s ∪ ts t := funext (λ x, !mem_to_set_union)

theorem mem_to_set_inter : (x ∈ ts (s ∩ t)) = (x ∈ ts s ∩ ts t) := !finset.mem_inter_eq
theorem to_set_inter : ts (s ∩ t) = ts s ∩ ts t := funext (λ x, !mem_to_set_inter)

theorem mem_to_set_diff : (x ∈ ts (s \ t)) = (x ∈ ts s \ ts t) := !finset.mem_diff_eq
theorem to_set_diff : ts (s \ t) = ts s \ ts t := funext (λ x, !mem_to_set_diff)

theorem mem_to_set_filter (p : A → Prop) [h : decidable_pred p] :
  (x ∈ ts (finset.filter p s)) = (x ∈ set.filter p (ts s)) := !finset.mem_filter_eq
theorem to_set_filter (p : A → Prop) [h : decidable_pred p] :
  ts (finset.filter p s) = set.filter p (ts s) := funext (λ x, !mem_to_set_filter)

theorem mem_to_set_image {B : Type} [h : decidable_eq B] (f : A → B) {s : finset A} {y : B} :
  (y ∈ ts (finset.image f s)) = (y ∈ set.image f (ts s)) := !finset.mem_image_eq
theorem to_set_image {B : Type} [h : decidable_eq B] (f : A → B) (s : finset A) :
  ts (finset.image f s) = set.image f (ts s) := funext (λ x, !mem_to_set_image)

/- relations -/

theorem mem_eq_mem_to_set : (x ∈ s) = (x ∈ ts s) := rfl

definition decidable_mem_to_set [instance] (x : A) (s : finset A) : decidable (x ∈ ts s) :=
decidable_of_decidable_of_eq _ !mem_eq_mem_to_set

theorem eq_eq_to_set_eq : (s = t) = (ts s = ts t) :=
propext (iff.intro
  (assume H, H ▸ rfl)
  (assume H, ext (take x, by rewrite [mem_eq_mem_to_set s, H])))

definition decidable_to_set_eq [instance] (s t : finset A) : decidable (ts s = ts t) :=
decidable_of_decidable_of_eq _ !eq_eq_to_set_eq

theorem subset_eq_to_set_subset (s t : finset A) : (s ⊆ t) = (ts s ⊆ ts t) :=
propext (iff.intro
  (assume H, take x xs, mem_of_subset_of_mem H xs)
  (assume H, subset_of_forall H))

definition decidable_to_set_subset (s t : finset A) : decidable (ts s ⊆ ts t) :=
decidable_of_decidable_of_eq _ !subset_eq_to_set_subset

/- bounded quantifiers -/

definition decidable_bounded_forall (s : finset A) (p : A → Prop) [h : decidable_pred p] :
  decidable (∀₀ x ∈ ts s, p x) :=
decidable_of_decidable_of_iff _ !all_iff_forall

definition decidable_bounded_exists (s : finset A) (p : A → Prop) [h : decidable_pred p] :
  decidable (∃₀ x ∈ ts s, p x) :=
decidable_of_decidable_of_iff _ !any_iff_exists

end finset