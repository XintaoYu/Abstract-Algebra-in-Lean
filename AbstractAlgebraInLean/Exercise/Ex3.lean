import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
-- Suppose G is a finite group
variable (G : Type) [Group G] [Fintype G] [DecidableEq G]
-- with even number of elements
example (h₀ : Even (Fintype.card G)):
-- Prove that there exists a ∈ G while a ≠ 1 such that a * a = 1
∃ a ≠ (1 : G), a * a = 1 := by
  -- By Cauchy's theorm we know if a prime number p divides the order of the group, then the group has an element with order p
  -- The order of G is even means there exists an element x with order 2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 <| Even.two_dvd h₀
  use x
  constructor
    -- If x = 1, then the order of x is 1, so x ≠ 1
  · rintro rfl
    simp at hx
    -- By definition of order, x ^ 2 = 1
  · rw [← sq, ← hx]
    exact pow_orderOf_eq_one x
