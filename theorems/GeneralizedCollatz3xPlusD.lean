-- ============================================================================
-- CONJECTURE #4 : GENERALIZED COLLATZ DYNAMICS (3x + d & 5x + 1) — PURE LEAN 4
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

def step3xPlusD (d n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + d

def iter3xPlusD (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter3xPlusD d k (step3xPlusD d n)

def Has3xPlusDDescent (d n : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ iter3xPlusD d k n < n

theorem step3xPlusD_even (d m : Nat) : step3xPlusD d (2 * m) = m := by
  simp only [step3xPlusD]
  split <;> omega

theorem step3xPlusD_odd (d m : Nat) : step3xPlusD d (2 * m + 1) = 3 * (2 * m + 1) + d := by
  simp only [step3xPlusD]
  split <;> omega

-- 1. Universal Even Descent (50% of all integers for ANY d)
theorem collatz3xPlusDEvenDescent (d m : Nat) (hm : 1 ≤ m) :
    iter3xPlusD d 1 (2 * m) < 2 * m := by
  simp only [iter3xPlusD, step3xPlusD_even]
  omega

-- 2. Universal Mod 4 Descent for d ≡ 1 (mod 8)
theorem collatz3xPlusDMod4Eq1Descent (j m : Nat) (hm : 2 * j + 1 ≤ m) :
    iter3xPlusD (8 * j + 1) 3 (4 * m + 1) < 4 * m + 1 := by
  have h0 : 4 * m + 1 = 2 * (2 * m) + 1 := by omega
  have h1 : 3 * (2 * (2 * m) + 1) + (8 * j + 1) = 2 * (6 * m + 4 * j + 2) := by omega
  have h2 : 6 * m + 4 * j + 2 = 2 * (3 * m + 2 * j + 1) := by omega
  simp only [iter3xPlusD]
  rw [h0, step3xPlusD_odd, h1, step3xPlusD_even, h2, step3xPlusD_even]
  omega

-- 3. Universal Mod 4 Descent for d ≡ 3 (mod 4)
theorem collatz3xPlusDMod4Eq3Descent (j m : Nat) (hm : j + 1 ≤ m) :
    iter3xPlusD (4 * j + 3) 3 (4 * m + 3) < 4 * m + 3 := by
  have h0 : 4 * m + 3 = 2 * (2 * m + 1) + 1 := by omega
  have h1 : 3 * (2 * (2 * m + 1) + 1) + (4 * j + 3) = 2 * (6 * m + 2 * j + 6) := by omega
  have h2 : 6 * m + 2 * j + 6 = 2 * (3 * m + j + 3) := by omega
  simp only [iter3xPlusD]
  rw [h0, step3xPlusD_odd, h1, step3xPlusD_even, h2, step3xPlusD_even]
  omega

-- 4. Universal Mod 8 Descent for d ≡ 1 (mod 16) on class 8m + 5
theorem collatz3xPlusDMod8Eq5Descent (j m : Nat) (hm : 2 * j + 1 ≤ m) :
    iter3xPlusD (16 * j + 1) 4 (8 * m + 5) < 8 * m + 5 := by
  have h0 : 8 * m + 5 = 2 * (4 * m + 2) + 1 := by omega
  have h1 : 3 * (2 * (4 * m + 2) + 1) + (16 * j + 1) = 2 * (12 * m + 8 * j + 8) := by omega
  have h2 : 12 * m + 8 * j + 8 = 2 * (6 * m + 4 * j + 4) := by omega
  have h3 : 6 * m + 4 * j + 4 = 2 * (3 * m + 2 * j + 2) := by omega
  simp only [iter3xPlusD]
  rw [h0, step3xPlusD_odd, h1, step3xPlusD_even, h2, step3xPlusD_even, h3, step3xPlusD_even]
  omega

-- 5. Crandall 5x + 1 Operator & Exact Non-Trivial 10-Step Cycles (n = 13 and n = 17)
def step5xPlus1 (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 5 * n + 1

def iter5xPlus1 : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter5xPlus1 k (step5xPlus1 n)

theorem crandall5xPlus1Cycle13 : iter5xPlus1 10 13 = 13 := by
  decide

theorem crandall5xPlus1Cycle17 : iter5xPlus1 10 17 = 17 := by
  decide

-- 6. Unconditional 75% Master Dichotomy for d ≡ 1 (mod 8)
theorem generalizedCollatz75PercentMasterTheorem (j n : Nat) (hn : 8 * j + 8 ≤ n) :
    Has3xPlusDDescent (8 * j + 1) n ∨ n % 4 = 3 := by
  by_cases h0 : n % 2 = 0
  · left
    refine ⟨1, by omega, ?_⟩
    have hn_eq : n = 2 * (n / 2) := by omega
    rw [hn_eq]
    exact collatz3xPlusDEvenDescent (8 * j + 1) (n / 2) (by omega)
  · by_cases h1 : n % 4 = 1
    · left
      refine ⟨3, by omega, ?_⟩
      have hn_eq : n = 4 * (n / 4) + 1 := by omega
      rw [hn_eq]
      exact collatz3xPlusDMod4Eq1Descent j (n / 4) (by omega)
    · right
      omega

-- 7. Symmetric 75% Master Dichotomy for d ≡ 3 (mod 4)
theorem generalizedCollatzMod4Eq3MasterTheorem (j n : Nat) (hn : 4 * j + 8 ≤ n) :
    Has3xPlusDDescent (4 * j + 3) n ∨ n % 4 = 1 := by
  by_cases h0 : n % 2 = 0
  · left
    refine ⟨1, by omega, ?_⟩
    have hn_eq : n = 2 * (n / 2) := by omega
    rw [hn_eq]
    exact collatz3xPlusDEvenDescent (4 * j + 3) (n / 2) (by omega)
  · by_cases h3 : n % 4 = 3
    · left
      refine ⟨3, by omega, ?_⟩
      have hn_eq : n = 4 * (n / 4) + 3 := by omega
      rw [hn_eq]
      exact collatz3xPlusDMod4Eq3Descent j (n / 4) (by omega)
    · right
      omega

#print axioms collatz3xPlusDEvenDescent
#print axioms collatz3xPlusDMod4Eq1Descent
#print axioms collatz3xPlusDMod4Eq3Descent
#print axioms collatz3xPlusDMod8Eq5Descent
#print axioms crandall5xPlus1Cycle13
#print axioms crandall5xPlus1Cycle17
#print axioms generalizedCollatz75PercentMasterTheorem
#print axioms generalizedCollatzMod4Eq3MasterTheorem
