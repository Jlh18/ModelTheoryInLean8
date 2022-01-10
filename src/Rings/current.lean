import Rings.AxGroth

namespace AxGroth

noncomputable theory

universe u

open fol
open Rings
open Fields

namespace current

-- local attribute [instance] classical.prop_decidable

variables {A : Type*} [comm_ring A]


def mv_polynomial_of_coeffs {n d : ℕ}
  (coeffs : dvector A (monom_deg_le n d).length) :
  mv_polynomial (fin n) A :=
-- sum indexed by the n-variable monom of degree < d
list.sumr
(list.map
  (
    λ f : (fin n → ℕ),
    -- each entry of the sum is a monomial f with "index-of-f-th"
    -- coefficient from "coeff"
    mv_polynomial.monomial (finsupp_of_fin_dom f)
      (coeffs.nth (list.index_of' f (monom_deg_le n d))
        (index_of_monom_deg_le_lt_length _))
  )
  (monom_deg_le n d)
)

lemma dvector.ith_chunk_aux {n m : ℕ} (i : fin n) (k : fin m) :
  i.val * m + ↑k < n * m :=
begin
  induction n with n hn,
  { apply fin_zero_elim i },
  {
    rw nat.succ_mul,
    cases fin.lt_or_eq_nat i with hi hi,
    {
      apply add_lt_add _ k.2,
      apply lt_of_le_of_lt _ (hn ⟨ i.1 , hi ⟩),
      apply le_add_right,
      apply le_of_eq,
      refl,
    },
    { rw [fin.val_eq_coe, hi, add_lt_add_iff_left],
      exact k.2, }
  }
end

def dvector.ith_chunk {α : Type*} {n m : ℕ} (i : fin n) (xs : dvector α (n * m)) :
  dvector α m :=
  dvector.of_fn (λ k, dvector.nth xs (i.1 * m + k) (dvector.ith_chunk_aux i k))

def list.ith_chunk {α : Type*} {n m : ℕ} (i : fin n)
  (xs : list α) (hlength : xs.length = n * m) :
  list α :=
list.of_fn (λ k, list.nth_le xs (i.1 * m + k)
  (by rw hlength; exact dvector.ith_chunk_aux i k))

lemma list.ith_chunk_length
  {α : Type*} {n m : ℕ} (i : fin n) (xs : list α) (hlength : xs.length = n * m)  :
  (list.ith_chunk i xs hlength).length = m :=
by simp only [list.ith_chunk, list.length_of_fn]

lemma list.ith_chunk_nth_le
  {α : Type*} {n m : ℕ} (i : fin n) (xs : list α) (hlength : xs.length = n * m)
  (l : ℕ) (hl : l < m) :
  list.nth_le (list.ith_chunk i xs hlength) l (by rw list.ith_chunk_length; exact hl) =
  xs.nth_le (i.1 * m + l) (by rw hlength; exact dvector.ith_chunk_aux i ⟨ l , hl ⟩) :=
by simpa only [list.ith_chunk, list.nth_le_of_fn']

lemma dvector.ith_chunk_nth {α : Type*} {n m : ℕ} (i : fin n) (xs : dvector α (n * m))
  (l : ℕ) (hl : l < m) :
  dvector.nth (dvector.ith_chunk i xs) l hl =
  xs.nth (i.1 * m + l) (dvector.ith_chunk_aux i ⟨ l , hl ⟩) :=
by simpa only [dvector.ith_chunk, dvector.nth_of_fn]

lemma mv_polynomial.total_degree_sum
  {A : Type*} {ι : Type*} {σ} [comm_semiring A] (s : finset ι)
  [decidable_eq ι]
  (ps : ι → mv_polynomial σ A) :
  (finset.sum s ps).total_degree
  ≤
  finset.sup s (mv_polynomial.total_degree ∘ ps) :=
finset.induction_on s (zero_le _)
(λ a s has hind, by rw finset.sum_insert has;
  exact le_trans (mv_polynomial.total_degree_add _ _)
    ( by rw [max_le_iff, finset.sup_insert];
      exact ⟨ le_sup_iff.mpr $ or.inl (le_of_eq rfl) , le_sup_iff.mpr $ or.inr hind ⟩))

section

lemma mv_polynomial.total_degree_monomial
  {A : Type*} [comm_semiring A] [decidable_eq A]
  {σ : Type*} (f : σ →₀ ℕ) (a : A) :
  (mv_polynomial.monomial f a).total_degree
  =
  ite (a = 0) ⊥ (f.sum (λ _ n, n)) :=
dite (a = 0)
(λ h, by rw [mv_polynomial.total_degree, mv_polynomial.support_monomial,
  if_pos h, if_pos h, finset.sup_empty])
(λ h, by rw [mv_polynomial.total_degree, mv_polynomial.support_monomial,
  if_neg h, if_neg h, finset.sup_singleton])

end

lemma mv_polynomial_of_coeffs_deg
  [decidable_eq A]
  {n d : ℕ}
  (coeffs : dvector A (monom_deg_le n d).length) (i : fin n) :
  (mv_polynomial_of_coeffs coeffs).total_degree ≤ d :=
begin
  simp only [mv_polynomial_of_coeffs,
    list.sumr_eq_sum, monom_deg_le, finset.sum_to_list],
  apply le_trans (mv_polynomial.total_degree_sum _ _),
  simp only [finset.sup_le_iff],
  intros f hf,
  simp only [function.comp],
  rw [mv_polynomial.total_degree_monomial],
  by_cases h :
    coeffs.nth (list.index_of' f (monom_deg_le_finset n d).to_list)
    (index_of_monom_deg_le_lt_length _) = 0,
  { simp only [if_pos h, bot_eq_zero, zero_le'] },
  { simp only [if_neg h, finsupp.sum],
    simp only [monom_deg_le_finset, finset.mem_filter] at hf,
    exact hf.2 },
  apply_instance, -- why??
end

axiom Ax_Groth_of_locally_finite
  {p : ℕ} (hprime : nat.prime p) (hchar : char_p A p) {n : ℕ}
  (ps : poly_map_data A n) (hinj : function.injective (poly_map ps)) :
  function.surjective (poly_map ps)
-- not the focus of the project

lemma realize_surj_formula_aux {n d : ℕ}
  (coeffs : dvector A (n * (monom_deg_le n d).length))
  (xs : dvector ↥(struc_to_ring_struc.Structure A) n)
  (ys : dvector ↥(struc_to_ring_struc.Structure A) n) (k : fin n) :
  realize_bounded_term
    (ys.append (xs.append coeffs))
    x_⟨ k + n , inj_formula_aux4 ⟩ dvector.nil
  = xs.nth' k :=
begin
    simp only [realize_bounded_term, symm (fin.val_eq_coe _)],
    rw dvector.nth_append_big (nat.le_add_left _ _) _,
    rw dvector.nth_append_small,
    { simp only [nat.add_sub_cancel,
      dvector.nth_of_fn, fin.val_eq_coe, fin.eta, dvector.nth'] },
    { rw nat.add_sub_cancel, exact k.2 },
end

def mv_polynomial.finsupp_coeff_add_zero_hom
  (A : Type*) [comm_semiring A] {σ} (f : σ →₀ ℕ) :
  add_zero_hom (mv_polynomial σ A) A :=
⟨ (λ p, mv_polynomial.coeff f p) , rfl , λ a b, rfl ⟩

lemma mv_polynomial.finsupp_coeff_sumr
  {A : Type*} [comm_semiring A] {σ} (f : σ →₀ ℕ)
  (ps : list (mv_polynomial σ A)) :
  mv_polynomial.coeff f ps.sumr
  =
  list.sumr (list.map (λ p : mv_polynomial σ A, mv_polynomial.coeff f p) ps) :=
list.add_zero_hom_sumr (mv_polynomial.finsupp_coeff_add_zero_hom A f) ps

lemma filter_coeff_monomial
  [decidable_eq A] {n d : ℕ} (a : (fin n → ℕ) → A)
  {f : fin n → ℕ} (hf : f ∈ monom_deg_le_finset n d) :
  (finset.filter
    (λ (x : fin n → ℕ),
      mv_polynomial.coeff (finsupp_of_fin_dom_emb f)
        (mv_polynomial.monomial (finsupp_of_fin_dom x) (a x))
        ≠ 0
    )
       (monom_deg_le_finset n d))
  = if a f = 0 then ∅ else { f }
  :=
begin
  simp only [mv_polynomial.coeff_monomial],
  by_cases hf0 : a f = 0,
  {
    simp only [if_pos hf0, finset.eq_empty_iff_forall_not_mem,
      finset.eq_singleton_iff_nonempty_unique_mem,
      finset.mem_filter, exists_prop, ite_eq_right_iff, ne.def, not_forall],
    intros x hx,
    obtain ⟨ _ , hx , hne ⟩ := hx,
    apply hne,
    rw ← hf0,
    congr,
    have hx' := congr_arg finsupp.equiv_fun_on_fintype hx,
    simp only [finsupp_of_fin_dom, finsupp_of_fin_dom_emb,
      equiv.to_embedding_apply, equiv.apply_symm_apply,
      equiv.inv_fun_as_coe] at hx',
    exact hx',
  },
  {
    simp only [if_neg hf0, finset.eq_singleton_iff_nonempty_unique_mem,
      finset.mem_filter, exists_prop, ite_eq_right_iff, ne.def, not_forall],
    split,
    {
      use f,
      simp only [finset.mem_filter],
      refine ⟨ hf , rfl , hf0 ⟩,
    },
    {
      intros x hx,
      obtain ⟨ _ , hx , _ ⟩ := hx,
      have hx' := congr_arg finsupp.equiv_fun_on_fintype hx,
      simp only [finsupp_of_fin_dom, finsupp_of_fin_dom_emb,
        equiv.to_embedding_apply, equiv.apply_symm_apply,
        equiv.inv_fun_as_coe] at hx',
      exact hx',
    },
  },
end

variable [decidable_eq A]

lemma mv_polynomial_of_coeffs_eq_nth_index_of'
  {n d : ℕ}
  (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length))
  (f : fin n → ℕ) (hf : f ∈ monom_deg_le_finset n d) (k : fin n) :
  (mv_polynomial_of_coeffs (dvector.ith_chunk k coeffs)).coeff
    (finsupp_of_fin_dom_emb f)
  =
  coeffs.nth
    (list.index_of' f (monom_deg_le_finset n d).to_list
      + ↑k * (monom_deg_le_finset n d).to_list.length)
      (poly_map_data.coeffs_dvector'_nth_aux0 _ _) :=
begin
  simp only [mv_polynomial_of_coeffs],
  rw mv_polynomial.finsupp_coeff_sumr,
  rw list.map_map,
  simp only [function.comp, list.sumr_eq_sum,
    monom_deg_le, finset.sum_to_list],
  rw ← finset.sum_filter_ne_zero,
  rw filter_coeff_monomial _ hf,
  by_cases h :
    (dvector.ith_chunk k coeffs).nth
      (list.index_of' f (monom_deg_le_finset n d).to_list)
      (index_of_monom_deg_le_lt_length _) = 0,
  {
    simp only [if_pos h, finset.sum_empty],
    rw dvector.ith_chunk_nth at h,
    simp only [add_comm
      (list.index_of' f (monom_deg_le_finset n d).to_list)
      (↑k * (monom_deg_le_finset n d).to_list.length)],
    convert symm h,
  },
  {
    simp only [if_neg h, finset.sum_singleton,
      mv_polynomial.coeff_monomial,
      finsupp_of_fin_dom, finsupp_of_fin_dom_emb],
    rw [dvector.ith_chunk_nth, if_pos],
    { congr1, apply add_comm },
    {refl},
  },
end

lemma eval_mv_polynomial_of_coeffs_ys0
  {n d : ℕ}
  (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length))
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n) (k : fin n) :
  mv_polynomial.eval ys.nth' (mv_polynomial_of_coeffs (dvector.ith_chunk k coeffs))
  =
  list.sumr (list.map
    (λ (f : fin n → ℕ),
      (ys.append (xs.append coeffs)).nth
        (list.index_of' f (monom_deg_le_finset n d).to_list +
           (k * (monom_deg_le_finset n d).to_list.length + n + n))
        (poly_indexed_by_monoms_aux0 n d _ _ inj_formula_aux0 f)
        *
        (n.non_comm_prod
          (λ (i : fin n),
            (ys.append (xs.append coeffs)).nth
            (i + 0) inj_formula_aux3 ^ f i))
        )
    (monom_deg_le_finset n d).to_list)
  :=
begin
  rw mv_polynomial.eval_eq',
  rw mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum _
    (mv_polynomial_of_coeffs_deg (dvector.ith_chunk k coeffs) k),
  rw finset.sum_map,
  delta monom_deg_le,
  rw list.sumr_eq_sum,
  rw finset.sum_to_list,
  apply finset.sum_congr rfl,
  intros f hf,
  rw realize_poly_map_data_coeffs_ys_aux_prod xs ys f,
  congr,
  rw dvector.nth_append_big,
  {
     rw dvector.nth_append_big,
     {
       simp only [add_assoc],
       simp only [symm (add_assoc (list.index_of' f (monom_deg_le_finset n d).to_list)
        (k * (monom_deg_le_finset n d).to_list.length ) (n + n))],
      simp only [symm (add_assoc (list.index_of' f (monom_deg_le_finset n d).to_list
        + k * (monom_deg_le_finset n d).to_list.length) n n)],
      simp only [nat.add_sub_cancel],
      rw mv_polynomial_of_coeffs_eq_nth_index_of' _ _ hf,
      refl,
      {apply_instance}, --why???
     },
     {
      rw ← add_assoc,
      rw nat.add_sub_cancel,
      rw ← add_assoc,
      apply nat.le_add_left,
    },
  },
  {
    rw ← add_assoc,
    apply nat.le_add_left,
  },
end

lemma eval_mv_polynomial_of_coeffs_xs0
  {n d : ℕ}
  (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length))
  (xs ys : dvector ↥(struc_to_ring_struc.Structure A) n) (k : fin n) :
  mv_polynomial.eval xs.nth' (mv_polynomial_of_coeffs (dvector.ith_chunk k coeffs))
  =
  list.sumr (list.map
    (λ (f : fin n → ℕ),
      (ys.append (xs.append coeffs)).nth
        (list.index_of' f (monom_deg_le_finset n d).to_list +
           (k * (monom_deg_le_finset n d).to_list.length + n + n))
        (poly_indexed_by_monoms_aux0 n d _ _ inj_formula_aux0 f)
        *
        (n.non_comm_prod
          (λ (i : fin n),
            (ys.append (xs.append coeffs)).nth
            (i + n) inj_formula_aux4 ^ f i))
        )
    (monom_deg_le_finset n d).to_list)
  :=
begin
  rw mv_polynomial.eval_eq',
  rw mv_polynomial_sum_eq_finset_map_monom_deg_le_finset_sum _
    (mv_polynomial_of_coeffs_deg (dvector.ith_chunk k coeffs) k),
  rw finset.sum_map,
  delta monom_deg_le,
  rw list.sumr_eq_sum,
  rw finset.sum_to_list,
  apply finset.sum_congr rfl,
  intros f hf,
  rw realize_poly_map_data_coeffs_xs_aux_prod xs ys f,
  congr,
  rw dvector.nth_append_big,
  {
     rw dvector.nth_append_big,
     {
       simp only [add_assoc],
       simp only [symm (add_assoc
         (list.index_of' f (monom_deg_le_finset n d).to_list)
         (k * (monom_deg_le_finset n d).to_list.length ) (n + n))],
      simp only [symm (add_assoc
        (list.index_of' f (monom_deg_le_finset n d).to_list
        + k * (monom_deg_le_finset n d).to_list.length) n n)],
      simp only [nat.add_sub_cancel],
      rw mv_polynomial_of_coeffs_eq_nth_index_of' _ _ hf,
      refl,
      {apply_instance}, --why???
     },
     {
      rw ← add_assoc,
      rw nat.add_sub_cancel,
      rw ← add_assoc,
      apply nat.le_add_left,
    },
  },
  {
    rw ← add_assoc,
    apply nat.le_add_left,
  },
end

lemma eval_mv_polynomial_of_coeffs_ys1
  {n d : ℕ} (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length))
  (xs : fin n → A)
  (ys : dvector ↥(struc_to_ring_struc.Structure A) n) (k : fin n) :
  mv_polynomial.eval ys.nth'
    (mv_polynomial_of_coeffs (dvector.ith_chunk k coeffs))
  =
  realize_bounded_term (ys.append ((dvector.of_fn xs).append coeffs))
    (poly_indexed_by_monoms n d
      (↑k * (monom_deg_le n d).length + n + n) 0
      (n * (monom_deg_le n d).length + n + n)
         inj_formula_aux0
         inj_formula_aux1)
      dvector.nil :=
by simpa only [realize_poly_indexed_by_monoms,
    eval_mv_polynomial_of_coeffs_ys0 _ (dvector.of_fn xs),
    monom_deg_le]

lemma eval_mv_polynomial_of_coeffs_xs1
  {n d : ℕ} (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length))
  (xs : fin n → A)
  (ys : dvector ↥(struc_to_ring_struc.Structure A) n) (k : fin n) :
  (mv_polynomial.eval xs) (mv_polynomial_of_coeffs (dvector.ith_chunk k coeffs))
  =
  realize_bounded_term (ys.append ((dvector.of_fn xs).append coeffs))
    (poly_indexed_by_monoms n d
      (↑k * (monom_deg_le n d).length + n + n) n
      (n * (monom_deg_le n d).length + n + n)
         inj_formula_aux0
         inj_formula_aux2)
      dvector.nil :=
begin
  rw ← dvector.nth'_of_fn1 xs,
  simp only [realize_poly_indexed_by_monoms,
    eval_mv_polynomial_of_coeffs_xs0 _ (dvector.of_fn xs) ys,
    monom_deg_le],
  simpa only [dvector.nth'_of_fn1],
end

lemma eval_mv_polynomial_of_coeffs_ys2
  {n d : ℕ} (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length))
  (xs : dvector (struc_to_ring_struc.Structure A) n)
  (ys : fin n → (struc_to_ring_struc.Structure A)) (k : fin n) :
  (mv_polynomial.eval ys) (mv_polynomial_of_coeffs (dvector.ith_chunk k coeffs))
  =
  realize_bounded_term ((dvector.of_fn ys).append (xs.append coeffs))
      (poly_indexed_by_monoms n d (↑k * (monom_deg_le n d).length + n + n) 0 (n * (monom_deg_le n d).length + n + n)
         inj_formula_aux0
         inj_formula_aux1)
      dvector.nil :=
begin
  simp only [realize_poly_indexed_by_monoms, monom_deg_le],
  convert eval_mv_polynomial_of_coeffs_ys0 coeffs xs (dvector.of_fn ys) k,
  funext,
  rw dvector.nth'_of_fn,
end

lemma dvector.nth'_eq {α} {n} (ys : dvector α n) :
  (λ (i : fin n), ys.nth i i.2) = ys.nth' :=
begin
  funext, rw dvector.nth', refl,
end

lemma injective_iff_realize_inj_formula
  {n d : ℕ} (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length)) :
  function.injective
    (poly_map (λ i : fin n, mv_polynomial_of_coeffs (dvector.ith_chunk i coeffs)))
  ↔
  realize_bounded_formula coeffs (inj_formula n d) dvector.nil
  :=
begin
  simp only [inj_formula,
      realize_bounded_formula_bd_alls',
      realize_bounded_formula_bd_big_and,
      realize_bounded_formula],
  split,
  {
    intros hinj xs ys hImage k,
    have himage :
    poly_map
      (λ i : fin n, mv_polynomial_of_coeffs (dvector.ith_chunk i coeffs))
      (λ i, dvector.nth xs i i.2)
    =
    poly_map
      (λ i : fin n, mv_polynomial_of_coeffs (dvector.ith_chunk i coeffs))
      (λ i, dvector.nth ys i i.2),
   {
     funext j,
     convert hImage j,
     { simpa only [poly_map, dvector.nth'_eq,
         eval_mv_polynomial_of_coeffs_xs0 coeffs xs ys j,
         realize_poly_indexed_by_monoms,
         monom_deg_le] },
     { simpa only [poly_map, dvector.nth'_eq,
         eval_mv_polynomial_of_coeffs_ys0 coeffs xs ys j,
         realize_poly_indexed_by_monoms,
         monom_deg_le] },
   },
   have hpreimage := congr_fun (hinj himage) k,
   simp only [realize_bounded_term,
     @dvector.nth_append_small _ _ _ ys _ k k.2,
     dvector.nth_append_big (nat.le_add_left _ _),
     nat.add_sub_cancel,
     @dvector.nth_append_small _ _ _ xs _ k k.2],
   exact symm hpreimage,
  },
  {
    intros hInj xs ys himage,
    set ys' := dvector.of_fn ys with hys,
    set xs' := dvector.of_fn xs with hxs,
    have hImage : ∀ (k : fin n),
      realize_bounded_term (ys'.append (xs'.append coeffs))
        (poly_indexed_by_monoms n d (k * (monom_deg_le n d).length + n + n) n
          (n * (monom_deg_le n d).length + n + n)
          inj_formula_aux0
          inj_formula_aux2)
        dvector.nil =
      realize_bounded_term (ys'.append (xs'.append coeffs))
        (poly_indexed_by_monoms n d (k * (monom_deg_le n d).length + n + n) 0
          (n * (monom_deg_le n d).length + n + n)
          inj_formula_aux0
          inj_formula_aux1)
        dvector.nil,
    {
      intro j,
      convert congr_fun himage j,
     { simp only [poly_map, dvector.nth'_eq,
         eval_mv_polynomial_of_coeffs_xs1 coeffs xs ys' j,
         realize_poly_indexed_by_monoms,
         monom_deg_le] },
     {
       simp only [poly_map, dvector.nth'_eq,
         eval_mv_polynomial_of_coeffs_ys2 coeffs xs' ys j,
         realize_poly_indexed_by_monoms,
         monom_deg_le] },
    },
    funext k,
    have hPreimage := hInj xs' ys' hImage k,
    simp only [realize_bounded_term,
      @dvector.nth_append_small _ _ _ ys' _ k k.2,
      dvector.nth_append_big (nat.le_add_left _ _),
      nat.add_sub_cancel,
      @dvector.nth_append_small _ _ _ xs' _ k k.2,
      hys, hxs, dvector.nth_of_fn] at hPreimage,
    convert symm hPreimage,
    rw fin.eta k,
    rw fin.eta k,
  },
end

lemma surjective_iff_realize_surj_formula
  {n d : ℕ} (coeffs : dvector ↥(struc_to_ring_struc.Structure A)
    (n * (monom_deg_le n d).length)) :
  function.surjective
    (poly_map (λ i : fin n, mv_polynomial_of_coeffs (dvector.ith_chunk i coeffs)))
  ↔
  realize_bounded_formula coeffs (surj_formula n d) dvector.nil
  :=
begin
  simp only [surj_formula,
      realize_bounded_formula_bd_alls',
      realize_bounded_formula_bd_exs',
      realize_bounded_formula_bd_big_and,
      realize_bounded_formula],
  split,
  {
    intros hsurj xs,
    obtain ⟨ ys , hys ⟩ := hsurj (dvector.nth' xs),
    refine ⟨ dvector.of_fn ys , _ ⟩,
    intro k,
    have hysk := congr_fun hys k,
    simp only [poly_map] at hysk,
    rw realize_surj_formula_aux coeffs,
    convert hysk,
    rw eval_mv_polynomial_of_coeffs_ys2,
  },
  {
    intros hSurj xs,
    obtain ⟨ ys , hys ⟩ := hSurj (dvector.of_fn xs),
    refine ⟨ ys.nth' , _ ⟩,
    funext k,
    have hysk := hys k,
    simp only [poly_map],
    simp only [realize_surj_formula_aux coeffs (dvector.of_fn xs) ys k,
      dvector.nth'_of_fn] at hysk,
    convert hysk,
    rw [eval_mv_polynomial_of_coeffs_ys1],
  },
end

lemma realize_Ax_Groth_formula_of_char_p
  {K : Type*} [field K] [is_alg_closed K] [decidable_eq K]
  {p : ℕ} (hprime : nat.prime p) (hchar : char_p K p) (n d : ℕ) :
  struc_to_ring_struc.Structure K ⊨ Ax_Groth_formula n d :=
begin
  simp only [Ax_Groth_formula],
  simp only [realize_sentence_bd_alls],
  intro coeffs,
  simp only [realize_bounded_formula_imp],
  intro hinj,
  rw ← surjective_iff_realize_surj_formula,
  apply Ax_Groth_of_locally_finite hprime hchar,
  rw injective_iff_realize_inj_formula,
  exact hinj,
end

lemma ACFₚ_ssatisfied_Ax_Groth_formula (n d p : ℕ) (hp : nat.prime p) :
  (ACFₚ p) ⊨ Ax_Groth_formula n d :=
sorry
-- completeness of ACFₚ

lemma ACF₀_ssatisfied_Ax_Groth_formula (n d : ℕ) :
  ACF₀ ⊨ Ax_Groth_formula n d :=
sorry
-- lefschetz

lemma realize_Ax_Groth_formula_of_char_zero
  {K : Type*} [field K] [is_alg_closed K]
  (h0 : char_zero K) (n d : ℕ) :
  struc_to_ring_struc.Structure A ⊨ Ax_Groth_formula n d :=
sorry
-- soundness of ACF₀

end current

end AxGroth
