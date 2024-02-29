import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
-- Suppose G is a Group with finite elements
variable {α : Type}[Group G][Fintype G]
example
-- Suppose G has 4 elements
(h₀ : Fintype.card G = 4):
-- Prove that G is commute
∀ (a b : G), a * b = b * a := by
  -- Prove by contradiction
  by_contra h'
  push_neg at h'
  -- Suppose there exist a b ∈ G while a * b ≠ b * a
  rcases h' with ⟨a, b, not_commute⟩
  -- Have a ≠ b
  have aneb : a ≠ b := by
    -- Prove by contradiction
    by_contra h
    -- By assumption, get b * b ≠ b * b, leading to contradiction
    rw [h] at not_commute
    apply not_commute
    trivial
  -- Have a ≠ 1 and b ≠ 1
  have abne1 : a ≠ 1 ∧ b ≠ 1 := by
    -- Prove by contradiction. Use a = 1 / b = 1 in the not_commute assumption gets contradiction
    constructor <;> (by_contra h; rw [h] at not_commute; apply not_commute; simp)
  -- Have 1, a, b, a * b, b * a are distinct values
  have nodup : List.Nodup [1, a, b, a * b, b * a] := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, self_eq_mul_right,
      self_eq_mul_left, or_self, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
      and_true, or_false, or_self]; push_neg
    constructor
    · constructor
        -- a ≠ 1 is already proved
      · exact abne1.1.symm
      · constructor
          -- b ≠ 1 is already proved
        · exact abne1.2.symm
        · constructor
            -- Prove 1 ≠ a * b by contradiction
          · by_contra h
            -- By definition of group, b = a⁻¹
            have : b = a⁻¹ := eq_inv_of_mul_eq_one_right (id h.symm)
            -- Get a * b = b * a = a⁻¹ * a = a * a⁻¹ = 1, leading to contradiction
            apply not_commute; simp only [this, mul_right_inv, mul_left_inv]
            -- Prove 1 ≠ b * a is the same
          · by_contra h
            have : b = a⁻¹ := eq_inv_of_mul_eq_one_left (id h.symm)
            apply not_commute; simp only [this, mul_right_inv, mul_left_inv]
      -- a ≠ b, b ≠ 1, a ≠ 1, a * b ≠ b * a is already in assumption
    · constructor
      · exact ⟨aneb, abne1.2⟩
      · exact ⟨abne1.1, not_commute⟩
  -- There are 5 or more elements in G, leading to contradiction
  have : 5 ≤ Fintype.card G := by
    apply List.Nodup.length_le_card nodup
  rw [h₀] at this; contradiction
