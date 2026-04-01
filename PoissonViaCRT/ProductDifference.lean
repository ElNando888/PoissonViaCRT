/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Product-Difference Expansion

This file proves the finite product-difference identity: for `a b : ι → R` over a commutative ring
and a finite set `S`, the difference of products decomposes as a sum over nonempty subsets:

$$\prod_{i \in S} a_i - \prod_{i \in S} b_i
  = \sum_{\emptyset \neq T \subseteq S}
      \Bigl(\prod_{i \in T}(a_i - b_i)\Bigr)\,
      \Bigl(\prod_{i \in S \setminus T} b_i\Bigr).$$

## Main results

* `prod_sub_prod_expansion`: the identity above.
-/

open Finset in
/-- **Product-difference expansion.**
For a commutative ring `R`, a finset `S`, and functions `a b : ι → R`,

  `∏ i ∈ S, a i - ∏ i ∈ S, b i = ∑ T ∈ S.powerset.filter (· ≠ ∅),
      (∏ i ∈ T, (a i - b i)) * ∏ i ∈ S \ T, b i`

The proof rewrites `a i = (a i - b i) + b i`, applies `Finset.prod_add` to expand the product
over all subsets `T ⊆ S`, and then subtracts the `T = ∅` term (which is `∏ i ∈ S, b i`). -/
theorem prod_sub_prod_expansion {ι : Type*} {R : Type*} [CommRing R] [DecidableEq ι]
    (a b : ι → R) (S : Finset ι) :
    ∏ i ∈ S, a i - ∏ i ∈ S, b i =
      ∑ T ∈ S.powerset.filter (· ≠ ∅), (∏ i ∈ T, (a i - b i)) * ∏ i ∈ S \ T, b i := by
  have h_prod_add : ∏ i ∈ S, a i = ∑ T ∈ S.powerset, (∏ i ∈ T, (a i - b i)) * (∏ i ∈ S \ T, b i) := by
    convert Finset.prod_add _ _ _ using 2;
    ring;
  simp +decide [h_prod_add, Finset.filter_ne']