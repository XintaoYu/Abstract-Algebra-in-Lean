import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 引论

#check 1 -- Nat
#check Nat -- Type
#check 1 + 1 = 2 -- Prop
#check fun x ↦ x + 1 -- Nat → Nat
#check fun (x : Float) ↦ x + 1 -- Float → Float
#check fun x ↦ x

#check Nat.add  -- Nat → Nat → Nat
#check (Nat.add 1) -- Nat → Nat
#check (Nat.add 1 1) -- Nat
#eval Nat.add 1 1 -- 2

example : 1 + 1 = 2 := rfl

-- example : 1 + 1 = Nat.add 1 1 := by rfl
-- example : Nat.add 1 1 = Nat.succ (Nat.succ Nat.zero) := rfl
-- example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat'): Nat'

notation "α" => Nat'.succ (Nat'.zero)
notation "β" => Nat'.succ (Nat'.succ (Nat'.zero))

def Nat'.add (n k : Nat') : Nat' :=
  match k with
  | Nat'.zero => n
  | Nat'.succ k' => Nat'.succ  (Nat'.add n k')

example: Nat'.add α α = β := rfl
-- #eval Nat'.add α α = β


#check Nat.dvd_trans
-- Nat.dvd_trans {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c
#check Nat.dvd_mul_right
-- Nat.dvd_mul_right (a b : ℕ) : a ∣ a * b

example : ∀ (m n k : Nat), m ∣ n → m ∣ n * k :=
  fun m n k h ↦ Nat.dvd_trans h (Nat.dvd_mul_right n _)

example (m n k: Nat) : m ∣ n → m ∣ n * k :=
  fun h ↦ Nat.dvd_trans h (Nat.dvd_mul_right n _)

example (m n k: Nat) (h : m ∣ n) : m ∣ n * k :=
  Nat.dvd_trans h (Nat.dvd_mul_right n _)

example : ∀ (m n k : Nat), m ∣ n → m ∣ n * k := by
  intro m n k h
  apply dvd_mul_of_dvd_left h

example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  repeat rw [pow_two]
  rw [add_mul, mul_add, mul_add]
  rw [mul_comm b a, ← add_assoc, add_assoc (a * a), ← two_mul, ← mul_assoc]


example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  calc
    _ = a * a + a * b + b * a + b * b := by
      repeat rw [pow_two]
      rw [add_mul, mul_add, mul_add, ← add_assoc]
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by
      repeat rw [← pow_two]
      rw [mul_comm b a, add_assoc (a ^ 2), ← two_mul, ← mul_assoc]

example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

