import Mathlib
open Nat

/-
Let $n$ and $k$ be nonnegative integers with $k \leqslant n$. Then
(i ) $\binom{n}{0}=\binom{n}{n}=1$
(ii) $\binom{n}{k}=\binom{n}{n-k}$.
-/

-- these results are already present in Mathlib and `exact?` finds them
example (n k : ℕ) (_ : k ≤ n) : choose n n = choose n 0       := by exact (choose_symm_of_eq_add rfl)
example (n k : ℕ) (_ : k ≤ n) : choose n n = 1                := by exact choose_self n
example (n k : ℕ) (h : k ≤ n) : choose n (n - k) = choose n k := by exact choose_symm h
