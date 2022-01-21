import Rings.AxGroth
import completeness

----
namespace finset

variables {α : Type*}

lemma filter_mem_set_of_subset_set {s : set α} [decidable_pred (λ x, x ∈ s)]
  {fs : finset α} (h : ↑fs ⊆ s) :
  filter (λ x, x ∈ s) fs = fs :=
begin
  ext x,
  split,
  { apply filter_subset },
  { intro hmem, rw mem_filter, exact ⟨ hmem , h hmem ⟩ },
end

end finset
----

namespace fol

open fol

variables {L : Language}

namespace bounded_preformula

lemma bd_not.inj {n} {f0 f1 : bounded_formula L n} :
  ∼ f0 = ∼ f1 → f0 = f1 := λ h, (bd_imp.inj h).1

lemma bd_notequal.inj {n} {t0 t1 s0 s1 : bounded_term L n} :
  t0 ≄ s0 = t1 ≄ s1 → t0 = t1 ∧ s0 = s1 :=
bd_equal.inj ∘ bd_not.inj

end bounded_preformula

def is_complete' (T : Theory L) : Prop :=
∀ (ϕ : sentence L), T ⊨ ϕ ∨ T ⊨ ∼ ϕ

def is_complete'' (T : Theory L) : Prop :=
∀ (M : Structure L) (ϕ : sentence L), M ⊨ T → M ⊨ ϕ → T ⊨ ϕ

end fol

namespace Rings

def nat_ring_consts :
  ring_consts → dvector ℕ 0 → ℕ
| zero as := 0
-- | one as := 1

def nat_ring_structure_funcs :
  Π {n}, ring_signature.functions n → dvector ℕ n → ℕ
| 0 ring_consts.zero as := 0
| 0 ring_consts.one as := 1
| 1 ring_unaries.neg as := 0
| 2 ring_binaries.add (dvector.cons a (dvector.cons b nil)) := a + b
| 2 ring_binaries.mul (dvector.cons a (dvector.cons b nil)) := a * b
| (n+3) f as := pempty.elim f

def nat_ring_structure : fol.Structure ring_signature :=
⟨ ℕ , λ _, nat_ring_structure_funcs , λ _, pempty.elim ⟩

lemma nat_ring_structure_realize_nat :
  Π (n : ℕ) {k : ℕ} (v : dvector nat_ring_structure k),
  realize_bounded_ring_term v
    (n : fol.bounded_preterm ring_signature k 0) dvector.nil = n
| 0 _ _ := rfl
| (n+1) k v :=
begin
  have h := @nat_ring_structure_realize_nat n k v,
  rw [realize_bounded_ring_term] at h,
  simpa only [nat.cast_succ, ring_signature.add, realize_bounded_ring_term,
    fol.realize_bounded_term, h],
end

lemma nat_cast_bd_ring_term_inj {k n m : ℕ} :
  (n : fol.bounded_preterm.{0} ring_signature k 0) = ↑m → n = m :=
begin
  let v : dvector nat_ring_structure k := dvector.of_fn (λ i, 0),
  intro hnm,
  rw ← nat_ring_structure_realize_nat n v,
  rw ← nat_ring_structure_realize_nat m v,
  exact @congr_arg (fol.bounded_preterm ring_signature k 0)
    nat_ring_structure n m
    (λ t : fol.bounded_preterm ring_signature k 0,
      realize_bounded_ring_term v t dvector.nil) hnm,
end

end Rings

namespace Lefschetz

open fol
open Rings
open Fields

-- I imagine this is constructive but I don't want to spend time proving it
instance dec_eq_sentence_ring_signature :
  decidable_eq (sentence ring_signature) := sorry

lemma injective_plus_one_ne_zero : function.injective plus_one_ne_zero.{0} :=
begin
  intros n m himage,
  simp only [plus_one_ne_zero, ring_signature.one,
    ring_signature.add, ring_signature.zero] at himage,
  have h := (bd_app.inj (bd_app.inj (bd_notequal.inj himage).1).1).2,
  apply nat_cast_bd_ring_term_inj h,
end

-- lemma equal_instances_of_zero {M : Structure ring_signature} [mul_zero_class M] :
--   mul_zero_class.to_has_zero M.carrier = models_ring_theory_to_comm_ring.has_zero :=
-- begin

-- end
--
theorem is_complete'_ACF₀ : is_complete' ACF₀ :=
begin
  sorry
end

lemma characteristic_change_left (ϕ : sentence ring_signature.{0}) :
ACF₀ ⊨ ϕ → ∃ (n : ℕ), ∀ {p : ℕ} (hp : nat.prime p), n < p → ACFₚ hp ⊨ ϕ :=
begin
  rw compactness,
  intro hsatis,
  obtain ⟨ fs , hsatis , hsub ⟩ := hsatis,
  obtain ⟨ fsACF , fsrange , hunion, hACF , hrange ⟩ :=
    finset.subset_union_elim hsub,
  set fsnat : finset ℕ := finset.preimage fsrange plus_one_ne_zero.{0}
      (set.inj_on_of_injective injective_plus_one_ne_zero _) with hfsnat,
  use fsnat.sup id + 1,
  intros p hp hlt M hMx hmodel,
  have _inst_1 : fact (M ⊨ ACF) := ⟨ (models_ACFₚ_iff.mp hmodel).2 ⟩,
  have hchar := @models_ACFₚ_char _ _ _inst_1 _ hmodel,
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
      have hfield : field M.carrier := @models_ACF_to.Field _ _inst_1,
      apply @ring_char.lt_char_field _ (models_ACF_to.Field),
      { exact hbot },
      rw ← hchar at hx,
      exact hx,
    },
    apply hne_zero_of_le_char _,
    apply lt_of_le_of_lt (nat.succ_le_succ _) hlt,
    exact finset.le_sup hnp,
  },
end



/-- Any ring fact holds in ACF₀ if and only if for all large p it holds for all ACFₚ-/
theorem characteristic_change (ϕ : sentence ring_signature.{0}) :
ACF₀ ⊨ ϕ ↔ (∃ (n : ℕ), ∀ {p : ℕ} (hp : nat.prime p), n < p → ACFₚ hp ⊨ ϕ) :=
begin
  split,
  { apply characteristic_change_left },
  {
    intro hn,
    cases is_complete'_ACF₀ ϕ with hsatis hsatis,
    { exact hsatis },
    {
      have hm := characteristic_change_left (∼ ϕ) hsatis, clear hsatis, --R
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
      apply hm hn,
    },
  },
end




open Rings.ring_signature

lemma nat_cast_eq {M : Structure ring_signature} (n : ℕ)
  [non_assoc_semiring M.carrier] : (n : M)
  =
  (@nat.cast M.carrier (by apply_instance) _ _ n) := rfl

lemma something_spec {M : Structure ring_signature} (h : M ⊨ ACF)
  {p n : ℕ} (hp : prime p) (hchar : (p : M) = 0) (hnp : n < p) :
  (n : M) ≠ 0 :=
begin
  intro hn0,
  have hNASR : non_assoc_semiring M.carrier :=
  @semiring.to_non_assoc_semiring M (
    @comm_semiring.to_semiring M (
      @comm_ring.to_comm_semiring M (
        @field.to_comm_ring M (
          @models_ACF_to.Field M ⟨ h ⟩)))),
  have hrw := @ring_char.spec M hNASR n,
  rw @nat_cast_eq M n hNASR at hn0,
  -- rw hrw at hn0,

  -- rw hn0 at hrw,

  -- simp only [symm hn0] at hrw,
  sorry
end

example {R : Type*} [non_assoc_semiring R] (n : ℕ) : R := n.cast



#check ring_char.spec

#check char_p.exists_unique

end Lefschetz
