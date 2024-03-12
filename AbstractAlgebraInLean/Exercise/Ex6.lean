import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Subgroup.ZPowers
import Mathlib.Data.Nat.Totient

open Classical
-- Suppose we have a prime number p, a natural number r and let G = ℤ/p ^ r ℤ.
variable (p r : ℕ)(G : ZMod (p ^ r)) [h₀ : Fact (p.Prime)]
-- Let S denotes the set of all generators of G.
def S : Set (ZMod (p ^ r)) :=
  {n | AddSubgroup.zmultiples n = ⊤}

example
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
        rw [ZMod.int_cast_eq_int_cast_iff_dvd_sub (k * v.val) 1 (p ^ r)] at hk
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
          simp only [ZMod.nat_cast_val, Int.cast_add, Int.cast_mul,
            ZMod.int_cast_cast, ZMod.cast_id', id_eq, Int.cast_pow, Int.cast_ofNat]
          -- Since p ^ r is zero in G, then it is trivial.
          rw [ZMod.nat_cast_self (p ^ r)]
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
