import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic

section Ex1
-- Suppose that * is a binary operation on a set S.
variable {α : Type}(S : Set α)(f : α → α → α)
--Let H = {a ∈ S|a * x = x * a for all x ∈ S}.
def H : Set α :=
  {a | a ∈ S ∧ ∀ x ∈ S, f x a = f a x}
theorem Ex1
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
end Ex1

section Ex2
-- Suppose G is a Group with finite elements
variable {α : Type}[Group G][Fintype G]
theorem Ex2
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
end Ex2

section Ex3
-- Suppose G is a finite group
variable (G : Type) [Group G] [Fintype G] [DecidableEq G]
-- with even number of elements
theorem Ex3 (h₀ : Even (Fintype.card G)):
-- Prove that there exists a ∈ G while a ≠ 1 such that a * a = 1
∃ a ≠ (1 : G), a * a = 1 := by
  -- By Cauchy's theorm we know if a prime number p divides the order of the group, then the group has an element with order p
  -- The order of G is even means there exists an element x with order 2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 <| Even.two_dvd h₀
  use x
  constructor
    -- If x = 1, then the order of x is 1, so x ≠ 1
  · rintro rfl
    simp at hx
    -- By definition of order, x ^ 2 = 1
  · rw [← sq, ← hx]
    exact pow_orderOf_eq_one x
end Ex3

section Ex4
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
    simp only [HK]; simp only [HK] at ha; simp only [HK] at hb
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
      · simp only [ha₁, hb₁]
        exact mul_mul_mul_comm h₁ k₁ h₂ k₂
  -- Prove that 1 is an element of HK
  one_mem' := by
    -- Expand the definition of HK
    simp only [HK]
    -- Use 1 in H since H is a subgroup of G
    use 1
    constructor
    · exact Subgroup.one_mem H
    -- Use 1 in K since K is a subgroup of G
    · use 1
      constructor
      · exact Subgroup.one_mem K
        -- 1 = 1 * 1 is trival
      · simp only [mul_one]
  -- Prove there exists inverse element in HK for every a ∈ HK
  inv_mem' := by
    intro a ha
    simp only [HK]; simp only [HK] at ha
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
      · rw [ha₁]; simp only [mul_inv_rev, mul_comm]
end Ex4

section Ex5
-- Suppose G is a group
theorem Ex5 (G : Type) [Group G]
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
        -- If ⟨a⟩ is trivial, then a = 1, leading to contradiction
      · simp only [Subgroup.zpowers_eq_bot] at h₀ ; contradiction
        -- If ⟨a⟩ is nontrivial, since by assumption G is not cyclic, there exists x ∈ G while x ∉ ⟨a⟩
      · absurd (h' a); push_neg
        -- By assumption nontrivial ⟨a⟩ is G itself
        rw [h₀]
        -- x ∈ G but x ∉ ⟨a⟩ lead to contradiction
        exact fun _ => trivial
      -- If G is trivial
    · rw [nontrivial_iff] at hg
      push_neg at hg
      -- G only have element 1
      have : ∀ x : G, x = 1 := by exact fun x => hg x 1
      -- Thus G is a cyclic group generated by 1
      use 1
      simp only [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
      exact this
end Ex5

section Ex6
open Classical
-- Suppose we have a prime number p, a natural number r and let G = ℤ/p ^ r ℤ.
variable (p r : ℕ)(G : ZMod (p ^ r)) [h₀ : Fact (p.Prime)]
-- Let S denotes the set of all generators of G.
def S : Set (ZMod (p ^ r)) :=
  {n | AddSubgroup.zmultiples n = ⊤}

theorem Ex6
-- Suppose r is greater or equal to 1.
(h₁ : r ≥ 1):
  -- Prove that the cardinalty of S is p ^ (r - 1) * (p - 1).
  Fintype.card (S p r) = p ^ (r - 1)  * (p - 1) := by
  -- First we define a map from S to the subset of ℤ/p ^ r ℤ where each element is coprime with p ^ r,
  let trivialmap : S p r → {n // Nat.Coprime (ZMod.val n) (p ^ r)} := fun
    | .mk v h => {
      -- which is the identity map.
      val := v
      -- We need to prove if v is a generator of G, then it is coprime with p ^ r.
      property := by
        -- If v is a generator of G, then for any element x in G, there exists an integer k that k * v = x,
        simp [S, AddSubgroup.eq_top_iff', AddSubgroup.mem_zmultiples_iff] at h
        -- so we can fix a k that satisfies k * v = 1.
        rcases h 1 with ⟨k, hk⟩
        -- To prove v is coprime with p ^ r means to prove their greatest common divisor is 1.
        rw [Nat.coprime_iff_gcd_eq_one]
        rw [show ↑k * v = ((k * v.val):ℤ)   by simp, show (1:ZMod (p ^ r)) = (1 : ℤ) by simp ] at hk
        -- Since k * v and 1 are equal in ℤ/p ^ r ℤ, thus 1 - k * v can be divided by p ^ r.
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub (k * v.val) 1 (p ^ r)] at hk
        -- That means there exists an integer b that satisifes 1 - k * v = p ^ r * b.
        rcases hk with ⟨b, hb⟩
        simp at hb
        -- Equivalently we get 1 = k * v + p ^ r * b.
        have h' : k * v.val + b * ↑(p ^ r) = (1 : ℕ)  := by
          simp
          linarith
        -- Now we need to prove that the greatest common divisor of v and p ^ r can divide k * v + b * p ^ r.
        have : (Nat.gcd (ZMod.val v) (p ^ r) : ℤ ) ∣ (k * (ZMod.val v) + b * ↑(p ^ r)) := by
          -- By definition, the gcd can divide k * v and b * p ^ r
          have aux1 : ↑(Nat.gcd (ZMod.val v) (p ^ r)) ∣ (ZMod.val v : ℤ) := by
            apply Int.ofNat_dvd.mpr
            exact Nat.gcd_dvd_left (ZMod.val v) (p ^ r)
          have aux2 : (Nat.gcd (ZMod.val v) (p ^ r) : ℤ) ∣ ↑(p ^ r) := by
            apply Int.ofNat_dvd.mpr
            exact Nat.gcd_dvd_right (ZMod.val v) (p ^ r)
          -- Since the gcd can divide both of them, it can also divide their sum.
          apply Int.dvd_add
          · apply Int.dvd_trans aux1
            apply Int.dvd_mul_left
          · apply Int.dvd_trans aux2
            apply Int.dvd_mul_left
        -- Using the fact that k * v + b * p ^ r = 1, we get the gcd divides 1,
        rw [h'] at this
        rw [Int.ofNat_dvd] at this
        -- which means the greatest common divisor of v and p ^ r is 1. In other words, v is coprime with p ^ r.
        simp at this
        assumption
    }
  -- Next we define a map from the subset of G where each element is coprime with p ^ r to S.
  let trivialinverse : {n //  Nat.Coprime (ZMod.val n) (p ^ r)} → S p r := fun
    | .mk v h => {
      val := v
      -- We need to prove if v is coprime with p ^ r, then it is a generator of G.
      property := by
        -- To prove v is a generator of G means to prove for any element x ∈ G, there exists an integer k that k * v = x.
        simp [S]
        rw [AddSubgroup.eq_top_iff' _]
        intro x
        rw [AddSubgroup.mem_zmultiples_iff]
        -- The greatest common divisor of v and p ^ r is equal to a * v + b * p ^ r for some a b ∈ ℤ due to Bezout's theorem.
        have this := (Nat.gcd_eq_gcd_ab v.val (p ^ r)).symm
        -- For any x ∈ G, x * a is the k we need.
        use (x.val * Nat.gcdA v.val (p ^ r))
        simp
        -- Now we prove that a * v = 1 in ℤ/p ^ r ℤ.
        have : ↑(Nat.gcdA (ZMod.val v) (p ^ r)) * v  = 1 := by
          -- Since v and p ^ r are coprime, the gcd of v and p ^ r is one, which means a * v + b * p ^ r = 1.
          rw [Nat.Coprime.gcd_eq_one h] at this
          rw [show (1 : ZMod (p ^ r)) = (((1 : ℕ) : ℤ) : ZMod (p ^ r)) by simp ]
          -- Our goal is converted to prove a * v = a * v + b * p ^ r in ℤ/p ^ r ℤ.
          rw [this.symm]
          simp only [ZMod.natCast_val, Int.cast_add, Int.cast_mul,
            ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_pow, Int.cast_natCast]
          -- Since p ^ r is zero in G, then it is trivial.
          rw [ZMod.natCast_self ↑(p ^ r)]
          simp [mul_comm]
        rw [mul_assoc, this]
        simp
    }
  -- By the two maps which are inverse to each other, we get an isomorphism between S and the subset.
  let iso : S p r ≃ {n // Nat.Coprime (ZMod.val n) (p ^ r)} := {
    toFun := trivialmap
    invFun := trivialinverse
    left_inv := by
      intro a
      simp [trivialmap, trivialinverse]
    right_inv := by
      intro a
      simp [trivialmap, trivialinverse]
  }
  -- Then we prove the cardinalty of S is equal to the Euler's totient number of p ^ r.
  have : Fintype.card (S p r) = Nat.totient (p ^ r) := by
    calc
      -- So the cardinalty of S is equal to the subset.
      Fintype.card (S p r) = Fintype.card {n // Nat.Coprime (ZMod.val n) (p ^ r)} := (Fintype.card_congr iso)
      -- The subset is isomorphic to (ℤ/p ^ r ℤ)ˣ.
      _ = Fintype.card (ZMod (p ^ r))ˣ := (Fintype.card_congr ZMod.unitsEquivCoprime.symm)
      -- We know the cardinalty of (ℤ/p ^ r ℤ)ˣ is equal to the Euler's totient number of p ^ r,
      _ = Nat.totient (p ^ r) := ZMod.card_units_eq_totient _
  -- which is p ^ (r - 1) * (p - 1).
  rw [this]
  apply Nat.totient_prime_pow h₀.out; exact h₁
end Ex6


section Ex13
-- Suppose G is a group, a is an element in G.
variable  [Group G] (a : G)
-- Define f x that equals to a*x.
def f (x : G) : G := a * x
-- To prove f is bijective.
theorem Ex13 : (f a).Bijective := by
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
end Ex13
