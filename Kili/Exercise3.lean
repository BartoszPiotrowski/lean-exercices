import Mathlib

/-
We define a function recursively for all positive integers $n$ by $f(1)=1$,
$f(2)=5$, and for $n>2, f(n+1)=f(n)+2 f(n-1)$. Show that $f(n)=$
$2^{n}+(-1)^{n}$, using the second principle of mathematical induction.
-/

def f : ℕ → ℕ
  | 0 => 2 -- Lean requires to additionally specify the value for 0 as 0 ∈ ℕ
  | 1 => 1
  | 2 => 5
  | n + 1 => f n + 2 * f (n - 1)

example (n : ℕ) : (f n : ℤ)= 2 ^ n + (- 1) ^ n := by
-- we apply the second principle of mathematical induction:
induction' n using Nat.strong_induction_on with n ih
cases n with
| zero => simp [f] -- the case of n = 0
| succ n => cases n with
| zero => simp [f] -- the case of n = 1
| succ n => cases n with
| zero => simp [f] -- the case of n = 2
| succ n =>
simp [f]
have a := ih (n + 1) (by linarith)
have b := ih (n + 2) (by linarith)
rw [a, b]
ring
