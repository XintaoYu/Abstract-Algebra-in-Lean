import Mathlib.Tactic
-- Suppose G is a group
example (G : Type) [Group G]
-- G has no proper nontrivial subgroups
(h : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) :
-- Prove that G is cyclic
IsCyclic G := by
  -- To prove there exists a ∈ G that G = ⟨a⟩
  constructor
    -- Split the cases on whether G is nontrivial or not
  · by_cases hg : Nontrivial G
      -- If G is nontrivial, prove by contradiction
    · by_contra h'
      push_neg at h'
      -- Since G is nontrivial, G has an element a distinct from 1
      have exist_not_one : ∃ a : G, a ≠ 1 := exists_ne 1
      rcases exist_not_one with ⟨a, ha⟩
      -- By assumption, ⟨a⟩ as a subgroup of G is either trivial or G itself
      have : Subgroup.zpowers a = ⊥ ∨ Subgroup.zpowers a = ⊤ := h (Subgroup.zpowers a)
      rcases this with h₀ | h₀
        -- If ⟨a⟩ is trivial, then a = 1, leadding to contradiction
      · simp at h₀; contradiction
        -- If ⟨a⟩ is nonntrivial, then there exists x ∉ ⟨a⟩, which means ⟨a⟩ ≠ G, leading to contradiction
      · absurd (h' a); push_neg; rw [h₀]; exact fun x => trivial
      -- If G is trivial, then G only have element 1, which is cyclic
    · rw [nontrivial_iff] at hg
      push_neg at hg
      have : ∀ x : G, x = 1 := by exact fun x => hg x 1
      use 1
      exact fun x =>
        Exists.intro (Int.ofNat Nat.zero) (hg ((fun x => 1 ^ x) (Int.ofNat Nat.zero)) x)
