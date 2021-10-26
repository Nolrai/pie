import data.rat.basic
import data.nat.basic
import data.int.gcd
import data.nat.gcd
import data.nat.prime
import tactic

open_locale rat

open option

lemma two_is_two_over_one : 2 = 2 /. 1 := by {
  rw nat.cast_two.symm,
  rw rat.coe_nat_eq_mk,
  refl,
} 

lemma int.pos_of_div_pos (n m : ℤ) : 0 < m → 0 < n / m → 0 < n := by {
  intros m_pos n_m_pos,
  obtain (h | h | h) := (@trichotomous _ (<) _ 0 n),
  exact h,
  rw ← h at *, simp only [lt_self_iff_false, euclidean_domain.zero_div] at n_m_pos,
  cases n_m_pos,
  have : n / m < 0,
  rw int.div_lt_iff_lt_mul,
  rw zero_mul,
  repeat {assumption},
  exfalso,
  apply asymm this n_m_pos,
}

lemma rat.pos_of_mk_pos (n d : ℤ) : 0 < d → 0 < n /. d → 0 < n := by {
  intros d_pos n_d_pos,
  rw ← rat.num_pos_iff_pos at n_d_pos,
  lift d to ℕ,
  rw int.coe_nat_pos at d_pos,
  rw ← @rat.mk_pnat_eq n d d_pos at n_d_pos,
  rw rat.mk_pnat_num at n_d_pos,
  apply int.pos_of_div_pos n _ _ n_d_pos,
  rw int.coe_nat_pos,
  apply nat.gcd_pos_of_pos_right,
  simp only [pnat.mk_coe], assumption,
  apply le_of_lt; assumption,
}

lemma not_two_dvd_one : ¬ 2 ∣ 1 := by {
  intros h,
  obtain ⟨k, h⟩ := h,
  have : 1 % 2 = (2 * k) % 2,
  congr, exact h,
  apply (one_ne_zero : ¬ 1 = 0),
  transitivity 1 % 2,
  rw nat.mod_eq_of_lt one_lt_two,
  rw this,
  rw nat.mod_eq_zero_of_dvd,
  use k
}

lemma prime_dvd_of_dvd_sq {p n : ℕ} (p_prime : p.prime) (n_pos : 0 < n) (p_dvd_sq : p ∣ n * n) :
  p ∣ n := by 
{
  suffices : p ^ (0 + 1) ∣ n ∨ p ^ (0 + 1) ∣ n,
  {simp at this, exact this},
  have : p ^ 0 ∣ n := by {rw pow_zero, apply one_dvd},
  apply @nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p p_prime n n 0 0 this this,
  simp only [pow_one], exact p_dvd_sq,
}

lemma logic_aux {P Q R} : (P → Q → R) → P → (P → Q) → R :=
  λ pqr p pq, pqr p (pq p)

theorem rat.no_sqrt_of_two : ¬ ∃ q : ℚ, q * q = 2 := by {
  rw not_exists,
  suffices : (∀ q : ℚ, 0 < q → ¬ q * q = 2),
  {
    intro q,
    obtain (q_neg | q_zero | q_pos) := @trichotomous ℚ (<) _ q 0,
    {
      rw ← neg_mul_neg,
      apply this (-q),
      exact neg_pos.mpr q_neg,
    },
    {
      rw q_zero,
      simp,
    },
    exact this q q_pos,
  },
  intros q q_pos,
  revert q_pos,
  apply @rat.num_denom_cases_on _ q, clear q,
  intros n d d_pos n_d_coprime n_pos',
  have d_ne_zero : d ≠ 0 := ne_of_gt d_pos,
  rw two_is_two_over_one,
  have n_pos : 0 < n := by 
    {
      apply rat.pos_of_mk_pos n ↑d, 
      rw int.coe_nat_pos, 
      exact d_pos,
      exact n_pos'
    },
  clear n_pos',
  rw rat.mul_def,
  rw rat.mk_eq,
  rw mul_one,
  intros h,
  apply not_two_dvd_one,
  unfold nat.coprime at *,
  suffices : 2 ∣ n.nat_abs.gcd d,
  {
    rw n_d_coprime at *,
    exact this,
  },
  lift n to ℕ,
  all_goals {try {norm_cast at *}},
  apply logic_aux nat.dvd_gcd,
  apply prime_dvd_of_dvd_sq nat.prime_two n_pos,
  {
    {use d * d, exact h}
  },
  {
    intro two_dvd_n,
    apply prime_dvd_of_dvd_sq nat.prime_two d_pos,
    obtain ⟨k, n_eq_two_k⟩ := two_dvd_n,
    use (k * k),
    rw n_eq_two_k at h,
    rw mul_assoc at h,
    simp only [nat.one_ne_zero, mul_eq_mul_left_iff, or_false, bit0_eq_zero] at h,
    rw ← h,
    ring,
  },
  exact le_of_lt n_pos,
  exact mul_ne_zero d_ne_zero d_ne_zero,
}