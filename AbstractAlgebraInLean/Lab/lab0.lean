import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Exponential
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

-- example : 1 + 1 = Nat.add 1 1 := rfl
-- example : Nat.add 1 1 = Nat.succ (Nat.succ Nat.zero) := rfl
-- example : 2 = Nat.succ (Nat.succ Nat.zero) := rfl

inductive Nat' where
  | zero : Nat'
  | succ (n : Nat'): Nat'

def one' : Nat' := Nat'.succ Nat'.zero
def two' : Nat' := Nat'.succ (Nat'.succ Nat'.zero)

def Nat'.add (n k : Nat') : Nat' :=
  match k with
  | Nat'.zero => n
  | Nat'.succ k' => Nat'.succ  (Nat'.add n k')

example: Nat'.add one' one' = two' := rfl
-- #eval Nat'.add one' one' = two'


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

--如何证明不等式
--证明只含有数字的不等式
example : 2 + 1 < 5 := by
  norm_num   --使用norm_num完成对命题的证明


section
variable (a b c d e f : ℝ)
open Real
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans--apply作用在一个proof上，这个proof的结果要和当前的目标相同
  · apply h₀
  apply h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl x

variable (a b c d e f : ℝ)
open Real

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
--linarith用于不等式（或等式）的线性计算的化简,通过类似反证的方法，寻找矛盾，从而证明结论le_trans实则表示了不等号的传递性
example (h : a ≤ b) : exp a ≤ exp b := by
  apply exp_le_exp.mpr
  exact h
--exact作用在一个和当前目标相同的proof上来结束证明
--mp表示从左边推右边的对应的proof，即 exp_le_exp.mp {x y : \R} : rexp x <= rexp y -> x <= y
--.mpr表示从右边推左边的对应的proof，即 exp_le_exp.mpr {x y : \R} : x <= y -> rexp x <
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  have h₁: exp a ≤ exp b := by
    apply exp_le_exp.mpr
    apply h
  linarith
--have允许我们暂时忽略当前的目标，引入一个新的proof，并且把goal转变成这个proof，在我们证明引入的proof之后，可以利用引入的proof继续之前的证明

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h : a < c := by
    apply lt_of_le_of_lt h₀ h₁
  have h₄ : c < e := by
    apply lt_of_le_of_lt h₂ h₃
  apply lt_trans h h₄
  --也可使用lt_trans等来证明不等式
  --含有绝对值不等式的证明
example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel]
--或使用tactic ring简化计算
example : |a| - |b| ≤ |a - b| := by
  have h₀  : |a| - |b| + |b| ≤ |a - b| + |b|--先暂时把goal转变为|a| - |b| + |b| ≤ |a - b| + |b|
  calc--进行分布证明
    |a| - |b| + |b| ≤ |a - b + b| := by
      ring--使用ring简化计算
      apply le_refl
    _≤  |a - b| + |b|  := by
      apply abs_add--|x + y| ≤ |x| + |y|
  exact abs_sub_abs_le_abs_sub a b

--min与max的证明

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)


example : min a b = min b a := by
  apply le_antisymm--通过这个tactic将goal转变为min a b ≤ min b a和min b a ≤ min a b
  repeat--重复使用一下tactic
    apply le_min
    apply min_le_right
    apply min_le_left

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min--通过这个tactic将goal转变为min a b + c ≤ a + c和min a b + c ≤ b + c
  apply add_le_add_right--先对第一个goal进行证明
  apply min_le_left--证明min a b + c ≤ b + c
  apply add_le_add_right
  apply min_le_right
