import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.Init.Function
-- Suppose G is a group, a is an element in G.
variable  [Group G] (a : G)
-- Define f x that equals to a*x.
def f (x : G) : G := a * x
-- To prove f is bijective.
example : (f a).Bijective := by
  constructor
  -- To prove f is injective.
  ·-- f x = f y ,that is a*x = a*y , implies x = y by mul_left_cancel.
    intro x y h
    rw [f] at h
    rw [f] at h
    apply mul_left_cancel h

  --To prove f is surjective.
  · -- It suffices to show that every b is equal to f a .
    intro b
    -- f (a⁻¹ * b) = a * (a⁻¹ * b)
    use a⁻¹*b
    rw [f]
    -- = a * a⁻¹ * b
    rw [← mul_assoc]
    -- = 1 * b = b
    rw [mul_right_inv, one_mul]
