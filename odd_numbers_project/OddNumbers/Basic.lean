import Mathlib.Data.Nat.Basic
import OddNumbers.Parity
import Mathlib.Tactic.Ring  -- This import gives us access to the 'ring' tactic, which automates algebraic manipulations
-- A tactic is a command that tells Lean how to prove a goal.
-- The `ring` tactic is useful for simplifying expressions involving addition and multiplication
-- in rings, such as the natural numbers.
import Mathlib.Tactic.Linarith  -- For linear arithmetic reasoning
import Mathlib.Tactic.Cases     -- For case analysis

open Nat

/-- The square of an odd number is odd -/
theorem odd_square_of_odd (n : ℕ) (h : Odd n) : Odd (n * n) := by
  match h with
  | ⟨k, hk⟩ =>
    -- We claim that the square of n can be expressed as 2*(k*k + k) + 1
    exists 2 * k * k + 2 * k

    calc
      n * n = (2 * k + 1) * (2 * k + 1) := by rw [hk]
      _     = 4 * k * k + 4 * k + 1     := by ring
      _     = 2 * (2 * k * k + 2 * k) + 1 := by ring

theorem odd_mul_odd {m n : ℕ} (hm : Odd m) (hn : Odd n) : Odd (m * n) := by
  match hm, hn with
  | ⟨j, hj⟩, ⟨k, hk⟩ =>
    -- We claim that 2*j*k + j + k is the value that makes m*n = 2*(2*j*k + j + k) + 1
    exists 2 * j * k + j + k

    calc
      m * n = (2 * j + 1) * (2 * k + 1) := by rw [hj, hk]
      _     = 4 * j * k + 2 * j + 2 * k + 1 := by ring
      _     = 2 * (2 * j * k + j + k) + 1 := by ring

/-- Sum of the first n natural numbers: 0 + 1 + 2 + ... + (n-1) -/
def sum_n (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m+1 => sum_n m + m

open OddNumbers
theorem odd_sum_even {m n : ℕ } (hm: OddNumbers.Odd m) (hn: OddNumbers.Odd n) : OddNumbers.Even (m + n) := by
  match hm, hn with
  | ⟨j, hj⟩, ⟨k, hk⟩ =>
    -- We claim that the sum of m and n can be expressed as 2*(j + k + 1)
    exists (j + k + 1)

    calc
      m + n = (2 * j + 1) + (2 * k + 1) := by rw [hj, hk]
      _     = 2 * (j + k + 1) := by ring

theorem even_square_even (n : ℕ) (h : OddNumbers.Even n) : OddNumbers.Even (n * n) := by
  match h with
  | ⟨k, hk⟩ =>
    -- We claim that the square of n can be expressed as 2*(k*k)
    exists 2 * k * k

    calc
      n * n = (2 * k) * (2 * k) := by rw [hk]
      _     = 4 * k * k := by ring
      _     = 2 * (2 * k * k) := by ring

theorem even_mul_even {m n : ℕ} (hm : OddNumbers.Even m) (hn : OddNumbers.Even n) : OddNumbers.Even (m * n) := by
  match hm, hn with
  | ⟨j, hj⟩, ⟨k, hk⟩ =>
    -- We claim that the product of m and n can be expressed as 2*(j*k)
    exists 2 * j * k

    calc
      m * n = (2 * j) * (2 * k) := by rw [hj, hk]
      _     = 4 * j * k := by ring
      _     = 2 * (2 * j * k) := by ring

theorem even_sum_odd {m n : ℕ } (hm: OddNumbers.Even m) (hn: OddNumbers.Odd n) : OddNumbers.Odd (m + n) := by
  match hm, hn with
  | ⟨j, hj⟩, ⟨k, hk⟩ =>
    -- We claim that the sum of m and n can be expressed as 2*(j + k) + 1
    exists (j + k)

    calc
      m + n = (2 * j) + (2 * k + 1) := by rw [hj, hk]
      _     = 2 * (j + k) + 1 := by ring
