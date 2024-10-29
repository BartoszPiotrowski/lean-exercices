import Mathlib
open Finset BigOperators

/-
If $a$ and $r$ are real numbers and $r \neq 1$, then
$$
\sum_{j=0}^{n} a r^{j}=a+a r+a r^{2}+\cdots+a r^{n}=\frac{a r^{n+1}-a}{r-1}.
$$
-/

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) :
∑ i ∈ range (n + 1), a * r^i = (a * r^(n+1) - a) / (r-1) :=
  have h2 : r - 1 ≠ 0 := by exact sub_ne_zero_of_ne h
  by induction n with
  | zero =>
    simp
    rw [← mul_sub_one]
    rw [mul_div_cancel_of_imp]
    exact fun x ↦ False.elim (h2 x)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    rw [← mul_sub_one, ← mul_sub_one]
    rw [npow_add]
    field_simp
    ring



