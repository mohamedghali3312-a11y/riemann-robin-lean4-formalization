theorem lehmerNoOddSemiprime (p q : Nat) (hp : 3 ≤ p) (hq : p + 2 ≤ q) :
    ¬ ((p - 1) * (q - 1) ∣ p * q - 1) := by
  rintro ⟨k, hk⟩
  have h1 : p = (p - 1) + 1 := by omega
  have h2 : q = (q - 1) + 1 := by omega
  have h_expand : ((p - 1) + 1) * ((q - 1) + 1) =
                  (p - 1) * (q - 1) + ((p - 1) + (q - 1)) + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  rw [← h1, ← h2] at h_expand
  have h_rem_lt : (p - 1) + (q - 1) < (p - 1) * (q - 1) := by
    have hp1 : 2 ≤ p - 1 := by omega
    have hq1 : 4 ≤ q - 1 := by omega
    have h_mul : 2 * (q - 1) ≤ (p - 1) * (q - 1) := Nat.mul_le_mul_right (q - 1) hp1
    omega
  cases k with
  | zero =>
    simp only [Nat.mul_zero] at hk
    omega
  | succ k' =>
    cases k' with
    | zero =>
      simp only [Nat.mul_one] at hk
      omega
    
    | succ k'' =>
      have h_ge2 : (p - 1) * (q - 1) * (k'' + 1 + 1) =
                   (p - 1) * (q - 1) * k'' + ((p - 1) * (q - 1) + (p - 1) * (q - 1)) := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      omega
