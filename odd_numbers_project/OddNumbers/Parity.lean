import Mathlib.Data.Nat.Basic

namespace Nat

def OddNumbers.Odd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

def OddNumbers.Even (n : ℕ) : Prop := ∃ k, n = 2 * k

theorem odd_iff_exists_two_mul_add_one (n : ℕ) : OddNumbers.Odd n ↔ ∃ k, n = 2 * k + 1 :=
  -- The `Iff` constructor is used to create a logical equivalence
  Iff.refl _

end Nat
