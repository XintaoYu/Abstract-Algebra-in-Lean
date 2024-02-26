import Mathlib.Data.Set.Basic

-- Suppose that * is a binary operation on a set S.
variable {α : Type}(S : Set α)(f : α → α → α)
--Let H = {a ∈ S|a * x = x * a for all x ∈ S}.
def H : Set α :=
  {a | a ∈ S ∧ ∀ x ∈ S, f x a = f a x}
example
-- Suppose S is closed under *
(h₀ : ∀ {x y : α}, x ∈ S → y ∈ S → f x y ∈ S)
-- Suppose f is associative
(h₁ : ∀ {x y z : α}, x ∈ S → y ∈ S → z ∈ S → f (f x y) z = f x (f y z)):
-- Show that H is closed under *.
∀ (a b : α), a ∈ H S f → b ∈ H S f → f a b ∈ H S f:= by
  -- Let a b be the elements of Set H
  intro a b ha hb
  -- Expand the definition of H
  rw [H]
  -- First prove a * b ∈ S
  constructor
  · apply h₀ ha.1 hb.1
  -- Then prove a * b is commute with all elements in S
  intro x hx
  show f x (f a b) = f (f a b) x
  calc
    _ = f (f x a) b := by rw [← h₁ hx ha.1 hb.1]  -- x * (a * b)  =   x * a * b
    _ = f (f a x) b := by rw [ha.2 x hx]          -- x * a * b    =   a * x * b
    _ = f a (f x b) := by rw [h₁ ha.1 hx hb.1]    -- a * x * b    =   a * (x * b)
    _ = f a (f b x) := by rw [hb.2 x hx]          -- a * (x * b)  =   a * (b * x)
    _ = f (f a b) x := by rw [← h₁ ha.1 hb.1 hx]  -- a * (b * x)  =   a * b * x
