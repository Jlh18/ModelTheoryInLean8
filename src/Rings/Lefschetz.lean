import Rings.Fields
import completeness
import Rings.ToMathlib.finset

namespace Lefschetz

open fol
open Rings
open Fields
open Rings.instances

/-- Lefschetz part 1. Being true in a model of ACF₀ implies being true for any model of ACF₀-/
theorem is_complete''_ACF₀ : is_complete'' ACF₀ :=
by {rw ← is_complete''_iff_is_complete', exact is_complete'_ACF₀}

/-- Lefcschetz part 3. Being true in a model of ACFₚ implies being true for any model of ACFₚ-/
theorem is_complete''_ACFₚ {p : ℕ} (hp : nat.prime p) :
  is_complete'' (ACFₚ hp) :=
by {rw ← is_complete''_iff_is_complete', exact is_complete'_ACFₚ hp}

/-- Lefchetz part 2. A sentence holds for ACF₀ if and
  only if it holds for ACFₚ for large enough p (forward direction only) -/
theorem characteristic_change_left (ϕ : sentence ring_signature) :
ACF₀ ⊨ ϕ → ∃ (n : ℕ), ∀ {p : ℕ} (hp : nat.prime p), n < p → ACFₚ hp ⊨ ϕ :=
begin
  rw compactness,
  intro hsatis,
  obtain ⟨ fs , hsatis , hsub ⟩ := hsatis,
  classical,
  obtain ⟨ fsACF , fsrange , hunion, hACF , hrange ⟩ :=
    finset.subset_union_elim hsub,
  set fsnat : finset ℕ := finset.preimage fsrange plus_one_ne_zero
      (set.inj_on_of_injective injective_plus_one_ne_zero _) with hfsnat,
  use fsnat.sup id + 1,
  intros p hp hlt M hMx hmodel,
  haveI : fact (M ⊨ ACF) := ⟨ (models_ACFₚ_iff'.mp hmodel).2 ⟩,
  have hchar := (@models_ACFₚ_iff _ _ _inst_1 _).1 hmodel,
  apply hsatis hMx,
  rw [← hunion, finset.coe_union, all_realize_sentence_union],
  split,
  {
    apply all_realize_sentence_of_subset _ hACF,
    exact all_realize_sentence_of_subset hmodel ACF_subset_ACFₚ,
  },
  {
    have hSTS :(∀ n : ℕ, n ∈ fsnat → M ⊨ plus_one_ne_zero n) → M ⊨ fsrange,
    {
      classical,
      have hrw0 := finset.image_preimage plus_one_ne_zero fsrange
        (set.inj_on_of_injective injective_plus_one_ne_zero _),
      rw [← hfsnat, finset.filter_mem_set_of_subset_set (λ x hx, (hrange hx).1)]
        at hrw0,
      rw ← hrw0,
      simp only [all_realize_sentence],
      intros hrealize ϕ hϕ,
      simp only [set.mem_preimage, set.mem_image,
        finset.coe_preimage, finset.mem_coe, finset.coe_image] at hϕ,
      obtain ⟨ n , hn , hϕ ⟩ := hϕ,
      rw [← hϕ],
      apply hrealize,
      rw [hfsnat, finset.mem_preimage],
      exact hn,
    },
    apply hSTS,
    intros n hnp,
    rw realize_plus_one_ne_zero,
    have hne_zero_of_le_char :
      ∀ x : ℕ, x.succ < p → (x.succ : M) ≠ 0,
    {
      intros x hx hbot,
      apply nat.succ_ne_zero x,
      apply ring_char.lt_char_field hbot,
      rw ← hchar at hx,
      exact hx,
    },
    apply hne_zero_of_le_char _,
    apply lt_of_le_of_lt (nat.succ_le_succ _) hlt,
    exact finset.le_sup hnp,
  },
end

/-- Any ring fact holds in ACF₀ if and only if for all large p it holds for all ACFₚ-/
theorem characteristic_change (ϕ : sentence ring_signature) :
ACF₀ ⊨ ϕ ↔ (∃ (n : ℕ), ∀ {p : ℕ} (hp : nat.prime p), n < p → ACFₚ hp ⊨ ϕ) :=
begin
  split,
  { apply characteristic_change_left },
  {
    intro hn,
    cases is_complete'_ACF₀ ϕ with hsatis hsatis,
    { exact hsatis },
    { have hm := characteristic_change_left (∼ ϕ) hsatis,
      cases hn with n hn,
      cases hm with m hm,
      obtain ⟨ p , hle , hp ⟩ := nat.exists_infinite_primes (max n m).succ,
      have hnp : n < p :=
        lt_of_lt_of_le (nat.lt_succ_of_le (le_max_left _ _)) hle,
      have hmp : m < p :=
        lt_of_lt_of_le (nat.lt_succ_of_le (le_max_right _ _)) hle,
      have hS := instances.algebraic_closure_of_zmod_models_ACFₚ hp,
      specialize @hn p hp hnp _ ⟨ 0 ⟩ hS,
      specialize @hm p hp hmp _ ⟨ 0 ⟩ hS,
      simp only [realize_sentence_not] at hm,
      exfalso,
      apply hm hn } },
end

end Lefschetz
