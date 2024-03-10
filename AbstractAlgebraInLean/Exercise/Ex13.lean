import Mathlib.Tactic
import Mathlib.Algebra.Group.Basic
import Mathlib.Init.Function
-- Suppose G is a group, a is an element in G.
variable  [Group G] (a : G)
--Define f x that equals to a*x.
def f (x : G) : G := a * x

example : Function.Injective (f a) ∧ Function.Surjective (f a) := by
  constructor
  --To prove f is injective.
  ·--if f is injective, f x = f y implies x = y.
    intro x y h
    rw [f] at h
    rw [f] at h
    apply mul_left_cancel h

  --To prove f is surjective.
  · --if f is surjective,every b is equal to f a .
    intro b
    -- use a⁻¹*b in G since a and b are elements in G.
    use a⁻¹*b
    rw [f]
    rw [← mul_assoc]
    rw [mul_right_inv, one_mul]













  · intro
