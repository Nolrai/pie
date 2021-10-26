import data.rat.basic
import data.nat.basic
import data.int.gcd
import data.nat.gcd
import tactic

open_locale rat

open option

example : 2 = 2 /. 1 := by library_search

theorem rat.no_sqrt_of_two : ¬ ∃ q : ℚ, q * q = 2 := by {
  rw not_exists,
  intros q,
  apply @rat.num_denom_cases_on _ q, clear q,
  intros n d d_pos n_d_coprime,
  rw rat.coe_nat_eq_mk
}