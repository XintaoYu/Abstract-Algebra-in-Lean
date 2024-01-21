import AbstractAlgebraInLean.Common

class AddGroup₁ (α : Type) extends Add α, Zero α, Neg α where
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  zero_add : ∀ a : α, 0 + a = a
  add_zero : ∀ a : α, a + 0 = a
  add_left_neg : ∀ a : α, -a + a = 0

@[to_additive AddGroup₁]
class Group₁ (α : Type) extends One α, Mul α, Inv α  where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
  mul_left_inv : ∀ a : α, a⁻¹ * a = 1

class CommGroup₁ (α : Type) extends Group₁ α where
  mul_comm : ∀ a b : α, mul a b = mul b a

class CommAddGroup₁ (α : Type) extends AddGroup₁ α where
  add_comm : ∀ a b : α, add a b = add b a

export Group₁ (mul_assoc one_mul mul_one mul_left_inv)
export AddGroup₁ (add_assoc add_zero zero_add add_left_neg)

section Group₁

variable {G : Type} [Group₁ G] (a b c : G)

theorem mul_right_inv₁ : a * a⁻¹ = (1 : G) := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc a, ← mul_assoc a⁻¹ a, mul_left_inv a, one_mul a⁻¹, mul_left_inv (a * a⁻¹)]
  rw [← h, ← mul_assoc (a * a⁻¹)⁻¹, mul_left_inv (a * a⁻¹), one_mul (a * a⁻¹)]

example (h₁ : ∀ x : G, a * x = x ∧ x * a = x) (h₂ : ∀ x : G, b * x = x ∧ x * b = x) : a = b := by
  rw [← (h₁ b).1]
  nth_rw 1 [← (h₂ a).2]

lemma aux1 (h : a * b = 1) : b * a = 1 := by
  have h': (b * a)⁻¹ * (b * a * (b * a)) = 1  := by
    rw [mul_assoc b, ← mul_assoc a b, h, one_mul a, mul_left_inv (b * a)]
  rw [← h', ← mul_assoc (b * a)⁻¹, mul_left_inv (b * a), one_mul (b * a)]

lemma aux2 (h₁ : a * c = 1) (h₂ : b * c = 1) : a = b := by
  rw [← mul_one a, ← aux1 b c h₂, ← mul_assoc a, h₁, one_mul b]

lemma aux3 (h₁ : c * a = 1) (h₂ : c * b =1) : a = b := by
  rw [← mul_one a, ← h₂, ← mul_assoc a, aux1 c a h₁, one_mul b]

theorem inv_eq_of_mul  (h : a * b = 1) : a = b⁻¹ := aux2 a b⁻¹ b h (mul_left_inv b)
theorem inv_eq_of_mul' (h : a * b = 1) : b = a⁻¹ := aux3 b a⁻¹ a h (mul_right_inv₁ a)

theorem inv_of_inv : (a⁻¹)⁻¹ = a := aux2 a⁻¹⁻¹ a a⁻¹ (mul_left_inv a⁻¹) (mul_right_inv₁ a)

theorem mul_inv₁ : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (b⁻¹ * a⁻¹) * (a * b) = 1 := by
    rw [← mul_assoc (b⁻¹ * a⁻¹), mul_assoc b⁻¹, mul_left_inv a, mul_one b⁻¹, mul_left_inv b]
  apply aux2 (a * b)⁻¹ (b⁻¹ * a⁻¹) (a * b) (mul_left_inv (a * b)) h

theorem mul_right_cancel₁ (h : a * c = b * c) : a = b := by
  rw [← mul_one a, ← mul_right_inv₁ c, ← mul_assoc a, h, mul_assoc b, mul_right_inv₁, mul_one b]

theorem mul_left_cancel₁ (h : c * a = c * b) : a = b := by
  rw [← one_mul a, ← mul_left_inv c, mul_assoc c⁻¹, h, ← mul_assoc c⁻¹, mul_left_inv c, one_mul b]

end Group₁

section AddGroup₁

variable {G : Type}[AddGroup₁ G](a b c : G)

theorem add_right_neg₁ : a + -a = (0 : G) := by
  have h : -(a + -a) + (a + -a + a + -a) = 0 := by
    rw [add_assoc a, add_left_neg a, add_zero a, add_left_neg (a + -a)]
  rw [← h, add_assoc (a + -a), ← add_assoc (-(a + -a)), add_left_neg (a + -a), zero_add (a + -a)]

theorem neg_eq_of_add (h : a + b = 0) : b = -a := sorry
theorem neg_eq_of_add' (h : a + b = 0) : a = -b := sorry

theorem neg_of_neg : -(-a) = a := sorry

theorem add_right_cancel₁ (h : a + c = b + c) : a = b := sorry
theorem add_left_cancel₁ (h : c + a = c + b) : a = b := sorry

end AddGroup₁
