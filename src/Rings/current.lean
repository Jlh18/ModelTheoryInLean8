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

def weakly_complete (T : Theory L) : Prop :=
∀ (ϕ : sentence L), T ⊨ ϕ ∨ T ⊨ ∼ ϕ

def weakly_complete1 (T : Theory L) : Prop :=
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

/-- Any ring fact holds in ACF₀ if and only if for all large p it holds for all ACFₚ-/
theorem characteristic_change (ϕ : sentence ring_signature.{0}) :
ACF₀ ⊨ ϕ ↔ (∃ (n : ℕ), ∀ {p : ℕ} (hp : prime p), n < p → ACFₚ hp ⊨ ϕ) :=
begin
   split,
   {
     intro hsatis,
     rw compactness at hsatis,
     obtain ⟨ fs , hsatis , hsub ⟩ := hsatis,
     simp only [ACF₀] at hsub,
     obtain ⟨ fsACF , fsrange , hunion, hACF , hrange ⟩ :=
       finset.subset_union_elim hsub,
     set fsnat : finset ℕ := finset.preimage fsrange plus_one_ne_zero.{0}
         (set.inj_on_of_injective injective_plus_one_ne_zero _) with hfsnat,
     use fsnat.sup id + 1,
     intros p hp hlt,
     intros M hMx hmodel,
     apply hsatis hMx,
     rw [← hunion, finset.coe_union, all_realize_sentence_union],
     clear hsatis hsub,
     split,
     {
       apply all_realize_sentence_of_subset _ hACF,
       exact all_realize_sentence_of_subset hmodel ACF_subset_ACFₚ,
     },
     {
       --  any model of ACFₚ hp satisfies ∀ n < p, M ⊨ n ≠ 0
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
       have hrw1 : ∀ x : ℕ, M ⊨ plus_one_ne_zero x ↔ (x.succ : M) ≠ 0,
       { intro x, apply realize_plus_one_ne_zero },
       rw hrw1,
       rw models_ACFₚ_iff at hmodel,
       have hp : (p : M.carrier) = 0,
       sorry,
       have halg_cl : @is_alg_closed M (@models_ACF_to.Field M ⟨hmodel.2⟩) :=
         @models_ACF_to.is_alg_closed M ⟨hmodel.2⟩,

       -- have halg_closed : is_alg_closed M,
       have hne_zero_of_le_char : ∀ x : ℕ, x < p → (x : M.carrier) ≠ 0,
       sorry,
       apply hne_zero_of_le_char,
       apply lt_of_le_of_lt (nat.succ_le_succ _) hlt,
       have hrw2 : n = id n := rfl,
       rw hrw2,
       exact finset.le_sup hnp,
     },
   },
   sorry,
end

#check @finset.filter_subset


end Lefschetz
