import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

-- Let H K be the subgroups of an abelian group of G
variable {α : Type}[CommGroup G](H K : Subgroup G)
-- Define the set HK containing all the elements of h * k where h ∈ H, k ∈ K
def HK  :=
  {hk | ∃ h ∈ H, ∃ k ∈ K, hk = h * k}
-- Prove that HK is a subgroup of G
def subgroupHK :Subgroup G where
  carrier := HK H K
  -- Prove HK is closed under multiplication
  mul_mem' := by
    intro a b ha hb
    simp [HK]; simp [HK] at ha; simp [HK] at hb
    -- If a b ∈ HK, then a = h₁ * k₁, b = h₂ * k₂, where h₁ h₂ ∈ H, k₁ k₂ ∈ K
    rcases ha with ⟨h₁, hh₁,k₁, hk₁, ha₁⟩
    rcases hb with ⟨h₂, hh₂,k₂, hk₂, hb₁⟩
    -- h₁ * h₂ ∈ H since H is closed
    use h₁ * h₂
    constructor
    · exact Subgroup.mul_mem H hh₁ hh₂
      -- k₁ * k₂ ∈ K since K is closed
    · use k₁ * k₂
      constructor
      · exact Subgroup.mul_mem K hk₁ hk₂
        -- Since G is an abelian group, h₁ * h₂ * (k₁ * k₂) = h₁ * k₁ * (h₂ * k₂) = a * b
      · simp [ha₁, hb₁]
        exact mul_mul_mul_comm h₁ k₁ h₂ k₂
  -- Prove that 1 is an element of HK
  one_mem' := by
    -- Expand the definition of HK
    simp [HK]
    -- Use 1 in H since H is a subgroup of G
    use 1
    constructor
    · exact Subgroup.one_mem H
    -- Use 1 in K since K is a subgroup of G
    · use 1
      constructor
      · exact Subgroup.one_mem K
        -- 1 = 1 * 1 is trival
      · simp
  -- Prove there exists inverse element in HK for every a ∈ HK
  inv_mem' := by
    intro a ha
    simp [HK]; simp [HK] at ha
    -- Let a = h₁ * k₁ where h₁ ∈ H, k₁ ∈ K
    rcases ha with ⟨h₁, hh₁, k₁, hk₁, ha₁⟩
    -- Have h₁⁻¹ ∈ H since H is a Group
    use h₁⁻¹
    constructor
    · exact Subgroup.inv_mem H hh₁
      -- Have k₁⁻¹ ∈ K since K is a Group
    · use k₁⁻¹
      constructor
      · exact Subgroup.inv_mem K hk₁
        -- Since G is an abelian group, h₁⁻¹ * k₁⁻¹ = (h₁ * k₁)⁻¹
      · simp [ha₁, mul_comm]
