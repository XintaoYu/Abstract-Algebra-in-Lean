import AbstractAlgebraInLean.Common

class Group₁ (α : Type) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : α, mul one a = a
  mul_one : ∀ a : α, mul a one = a
  mul_left_inv : ∀ a : α, mul (inv a) a = one

class AddGroup₁ (α : Type) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ a b c : α, add (add a b) c = add a (add b c)
  zero_add : ∀ a : α, add zero a = a
  add_zero : ∀ a : α, add a zero = a
  add_left_neg : ∀ a : α, add (neg a) a = zero

infixl:70 " * " => Group₁.mul
infixl:65 " + " => AddGroup₁.add
postfix:max "⁻¹" => Group₁.inv
prefix:75 "-" => AddGroup₁.neg

notation "𝟙" => Group₁.one
notation "𝟘" => AddGroup₁.zero

class CommGroup₁ (α : Type) extends Group₁ α where
  mul_comm : ∀ a b : α, mul a b = mul b a

class CommAddGroup₁ (α : Type) extends AddGroup₁ α where
  add_comm : ∀ a b : α, add a b = add b a

section Group₁

variable {α : Type}[Group₁ α](a b c : α)

theorem mul_assoc₁ : a * b * c = a * (b * c) := Group₁.mul_assoc a b c

theorem one_mul₁ : (𝟙 : α) * a = a := Group₁.one_mul a

theorem mul_one₁ : a * (𝟙 : α) = a := Group₁.mul_one a

theorem mul_left_inv₁ : a⁻¹ * a = (𝟙 : α) := Group₁.mul_left_inv a

theorem mul_right_inv₁ : a * a⁻¹ = (𝟙 : α) := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 𝟙 := by
    rw [mul_assoc₁, ← mul_assoc₁ a⁻¹ a, mul_left_inv₁, one_mul₁, mul_left_inv₁]
  rw [← h, ← mul_assoc₁, mul_left_inv₁, one_mul₁]

example (h₁ : ∀ x : α, a * x = x ∧ x * a = x) (h₂ : ∀ x : α, b * x = x ∧ x * b = x) : a = b := by
  rw [← (h₁ b).1]
  nth_rw 1 [← (h₂ a).2]

lemma aux1 (h : a * b = 𝟙) : b * a = 𝟙 := by
  have h': (b * a)⁻¹ * (b * a * (b * a)) = 𝟙  := by
    rw [mul_assoc₁, ← mul_assoc₁ a b, h, one_mul₁, mul_left_inv₁]
  rw [← h', ← mul_assoc₁, mul_left_inv₁, one_mul₁]

lemma aux2 (h₁ : a * c = 𝟙) (h₂ : b * c = 𝟙) : a = b := by
  rw [← mul_one₁ a, ← aux1 b c h₂, ← mul_assoc₁, h₁, one_mul₁]

lemma aux3 (h₁ : c * a = 𝟙) (h₂ : c * b =𝟙) : a = b := by
  rw [← mul_one₁ a, ← h₂, ← mul_assoc₁, aux1 c a h₁, one_mul₁]

theorem inv_def (h : a * b = 𝟙) : a = b⁻¹ := aux2 a b⁻¹ b h (mul_left_inv₁ b)
theorem inv_def' (h : a * b = 𝟙) : b = a⁻¹ := aux3 b a⁻¹ a h (mul_right_inv₁ a)

theorem inv_of_inv : (a⁻¹)⁻¹ = a := aux2 a⁻¹⁻¹ a a⁻¹  (mul_left_inv₁ a⁻¹) (mul_right_inv₁ a)

theorem mul_inv₁ : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (b⁻¹ * a⁻¹) * (a * b) = 𝟙 := by
    rw [← mul_assoc₁, mul_assoc₁ b⁻¹, mul_left_inv₁, mul_one₁, mul_left_inv₁]
  apply aux2 (a * b)⁻¹ (b⁻¹ * a⁻¹) (a * b) (mul_left_inv₁ (a * b)) h

theorem mul_right_cancel₁ (h : a * c = b * c) : a = b := by
  rw [← mul_one₁ a, ← mul_right_inv₁ c, ← mul_assoc₁, h, mul_assoc₁, mul_right_inv₁, mul_one₁]

theorem mul_left_cancel₁ (h : c * a = c * b) : a = b := by
  rw [← one_mul₁ a, ← mul_left_inv₁ c, mul_assoc₁, h, ← mul_assoc₁, mul_left_inv₁, one_mul₁]

end Group₁

section AddGroup₁

variable {α : Type}[AddGroup₁ α](a b c : α)

theorem add_assoc₁ : a + b + c = a + (b + c) := AddGroup₁.add_assoc a b c

theorem zero_add₁ : (𝟘 : α) + a = a := AddGroup₁.zero_add a

theorem add_zero₁ : a + (𝟘 : α) = a := AddGroup₁.add_zero a

theorem add_left_neg₁ : -a + a = (𝟘 : α) := AddGroup₁.add_left_neg a

theorem add_right_neg₁ : a + -a = (𝟘 : α) := by
  have h : -(a + -a) + (a + -a + a + -a) = 𝟘 := by
    rw [add_assoc₁ a, add_left_neg₁, add_zero₁, add_left_neg₁]
  rw [← h, add_assoc₁, ← add_assoc₁, add_left_neg₁, zero_add₁]

end AddGroup₁
