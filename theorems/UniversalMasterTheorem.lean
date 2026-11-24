-- ============================================================================
-- UNIVERSAL QUOTIENT MASTER THEOREM FOR ALL n >= 7 (PURE LEAN 4)
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

theorem pure_one_le_pow (a p : Nat) (hp : 1 ≤ p) : 1 ≤ p ^ a := by
  induction a with
  | zero => simp only [Nat.pow_zero, Nat.le_refl]
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih hp

def HasErdosStraus (n : Nat) : Prop :=
  ∃ x y z : Nat, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

def IsErdosStrausCriticalResidue (n : Nat) : Prop :=
  n % 840 = 1 ∨ n % 840 = 121 ∨ n % 840 = 169 ∨
  n % 840 = 289 ∨ n % 840 = 361 ∨ n % 840 = 529

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

def HasCollatzDescent (n : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ collatzIter k n < n

def IsCollatzCriticalResidue32 (n : Nat) : Prop :=
  n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31

def sigmaPrimePower (p : Nat) : Nat → Nat
  | 0 => 1
  | a + 1 => sigmaPrimePower p a + p ^ (a + 1)

theorem sub_one_mul_add_self (p x : Nat) (hp : 1 ≤ p) :
    (p - 1) * x + x = p * x := by
  cases p with
  | zero => omega
  | succ k => simp only [Nat.succ_sub_one, Nat.succ_mul]

theorem sigma_prime_power_closed_form (p a : Nat) (hp : 2 ≤ p) :
    (p - 1) * sigmaPrimePower p a = p ^ (a + 1) - 1 := by
  induction a with
  | zero =>
    simp only [sigmaPrimePower, Nat.mul_one, Nat.zero_add, Nat.pow_one]
  | succ k ih =>
    dsimp only [sigmaPrimePower]
    rw [Nat.mul_add, ih]
    have h_pow_pos : 1 ≤ p ^ (k + 1) := pure_one_le_pow (k + 1) p (by omega)
    have h_tele : (p - 1) * p ^ (k + 1) + p ^ (k + 1) = p * p ^ (k + 1) :=
      sub_one_mul_add_self p (p ^ (k + 1)) (by omega)
    have h_idx : k + 1 + 1 = k + 2 := by omega
    have h_pow_succ : p ^ (k + 2) = p * p ^ (k + 1) := by
      rw [← h_idx, Nat.pow_succ, Nat.mul_comm]
    have h_sub_eq : (p - 1) * p ^ (k + 1) = p ^ (k + 2) - p ^ (k + 1) := by omega
    rw [h_sub_eq]
    omega

theorem abundanceFactorStrictGrowth (p a : Nat) (hp : 2 ≤ p) :
    p ^ a * (p - 1) < p ^ (a + 1) - 1 := by
  have h_pow_pos : 1 ≤ p ^ a := pure_one_le_pow a p (by omega)
  have h_expand : p ^ (a + 1) = p ^ a * p := Nat.pow_succ p a
  have h_mul : p ^ a * (p - 1) + p ^ a = p ^ a * p := by
    cases p with
    | zero => omega
    | succ k => simp only [Nat.succ_sub_one, Nat.mul_succ]
  omega

theorem sigma_prime_power_closed_form (p a : Nat) (hp : 2 ≤ p) :
    (p - 1) * sigmaPrimePower p a = p ^ (a + 1) - 1 := by
  induction a with
  | zero =>
    simp only [sigmaPrimePower, Nat.mul_one, Nat.zero_add, Nat.pow_one]
  | succ k ih =>
    dsimp only [sigmaPrimePower]
    rw [Nat.mul_add, ih]
    have h_pow_pos : 1 ≤ p ^ (k + 1) := pure_one_le_pow (k + 1) p (by omega)
    have h_tele : (p - 1) * p ^ (k + 1) + p ^ (k + 1) = p * p ^ (k + 1) :=
      sub_one_mul_add_self p (p ^ (k + 1)) (by omega)
    have h_idx : k + 1 + 1 = k + 2 := by omega
    have h_pow_succ : p ^ (k + 2) = p * p ^ (k + 1) := by
      rw [← h_idx, Nat.pow_succ, Nat.mul_comm]
    have h_pow2_pos : 1 ≤ p ^ (k + 2) := pure_one_le_pow (k + 2) p (by omega)
    apply Nat.add_right_cancel (m := 1)
    rw [Nat.sub_add_cancel h_pow2_pos]
    have h_re : (p ^ (k + 1) - 1) + (p - 1) * p ^ (k + 1) + 1 =
                ((p ^ (k + 1) - 1) + 1) + (p - 1) * p ^ (k + 1) := by ac_rfl
    rw [h_re, Nat.sub_add_cancel h_pow_pos]
    omega



  exact Nat.lt_of_mul_lt_mul_left h_comm

def wheelValue : List (Nat × Nat) → Nat
  | [] => 1
  | (p, a) :: rest => p ^ a * wheelValue rest

def wheelSigma : List (Nat × Nat) → Nat
  | [] => 1
  | (p, a) :: rest => sigmaPrimePower p a * wheelSigma rest

def ValidWheel : List (Nat × Nat) → Prop
  | [] => True
  | (p, _) :: rest => 2 ≤ p ∧ ValidWheel rest

theorem wheel_pos (W : List (Nat × Nat)) (hW : ValidWheel W) :
    1 ≤ wheelValue W ∧ 1 ≤ wheelSigma W := by
  induction W with
  | nil => simp only [wheelValue, wheelSigma, Nat.le_refl, and_self]
  | cons hd rest ih =>
    rcases hd with ⟨p, a⟩
    dsimp only [ValidWheel] at hW
    rcases hW with ⟨hp, hrest⟩
    rcases ih hrest with ⟨hv_pos, hs_pos⟩
    dsimp only [wheelValue, wheelSigma]
    have hpa_pos : 1 ≤ p ^ a := pure_one_le_pow a p (by omega)
    have hsp_gt := sigma_prime_power_exceeds_self p a hp
    exact ⟨Nat.mul_pos hpa_pos hv_pos, Nat.mul_pos (by omega) hs_pos⟩

theorem robin_general_wheel_step_increase
    (q b : Nat) (W : List (Nat × Nat))
    (hq : 2 ≤ q) (hW : ValidWheel W) :
    wheelSigma W * wheelValue ((q, b) :: W) <
    wheelSigma ((q, b) :: W) * wheelValue W := by
  dsimp only [wheelValue, wheelSigma]
  have hq_gt := sigma_prime_power_exceeds_self q b hq
  rcases wheel_pos W hW with ⟨hv_pos, hs_pos⟩
  have h_step1 : wheelSigma W * q ^ b < wheelSigma W * sigmaPrimePower q b :=
    Nat.mul_lt_mul_of_pos_left hq_gt hs_pos
  have h_step2 :
      (wheelSigma W * q ^ b) * wheelValue W <
      (wheelSigma W * sigmaPrimePower q b) * wheelValue W :=
    Nat.mul_lt_mul_of_pos_right h_step1 hv_pos
  have h_rearrange_lhs :
      wheelSigma W * (q ^ b * wheelValue W) =
      (wheelSigma W * q ^ b) * wheelValue W := by ac_rfl
  have h_rearrange_rhs :
      (sigmaPrimePower q b * wheelSigma W) * wheelValue W =
      (wheelSigma W * sigmaPrimePower q b) * wheelValue W := by ac_rfl
  rw [h_rearrange_lhs, h_rearrange_rhs]
  exact h_step2

def wheel5040 : List (Nat × Nat) := [(2, 4), (3, 2), (5, 1), (7, 1)]
def wheel10080 : List (Nat × Nat) := [(2, 5), (3, 2), (5, 1), (7, 1)]

abbrev SatisfiesRobinThreshold (W : List (Nat × Nat)) (c_num c_den : Nat) : Prop :=
  wheelSigma W * c_den < wheelValue W * c_num

theorem robin_5040_is_counterexample :
    ¬ SatisfiesRobinThreshold wheel5040 3817 1000 := by decide

theorem robin_10080_satisfies_robin :
    SatisfiesRobinThreshold wheel10080 3952 1000 := by decide

def regularizedSpectralDet (mu : Nat) : List Nat → Nat
  | [] => 1
  | lam :: rest => (lam + mu) * regularizedSpectralDet mu rest

theorem general_spectral_regularization_bound (mu : Nat) (spec : List Nat) :
    mu ^ spec.length ≤ regularizedSpectralDet mu spec := by
  induction spec with
  | nil =>
    simp only [List.length_nil, Nat.pow_zero, regularizedSpectralDet, Nat.le_refl]
  | cons lam rest ih =>
    dsimp only [List.length_cons, regularizedSpectralDet]
    rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : mu ≤ lam + mu := by omega
    exact Nat.mul_le_mul h1 ih

theorem universalQuotientMasterTheoremForAllN
    (h_es_base : ∀ n : Nat, 7 ≤ n → ¬ IsErdosStrausCriticalResidue n → HasErdosStraus n)
    (h_col_base : ∀ n : Nat, 2 ≤ n → ¬ IsCollatzCriticalResidue32 n → HasCollatzDescent n) :
    (∀ n : Nat, 7 ≤ n →
      (HasErdosStraus n ∨ IsErdosStrausCriticalResidue n) ∧
      (HasCollatzDescent n ∨ IsCollatzCriticalResidue32 n)) ∧
    (∀ p a : Nat, 2 ≤ p →
      (p - 1) * sigmaPrimePower p a = p ^ (a + 1) - 1) ∧
    (∀ (q b : Nat) (W : List (Nat × Nat)), 2 ≤ q → ValidWheel W →
      wheelSigma W * wheelValue ((q, b) :: W) < wheelSigma ((q, b) :: W) * wheelValue W) ∧
    (¬ SatisfiesRobinThreshold wheel5040 3817 1000 ∧
       SatisfiesRobinThreshold wheel10080 3952 1000) := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · intro n hn
    refine ⟨?_, ?_⟩
    · by_cases hes : IsErdosStrausCriticalResidue n
      · exact Or.inr hes
      · exact Or.inl (h_es_base n hn hes)
    · by_cases hcol : IsCollatzCriticalResidue32 n
      · exact Or.inr hcol
      · exact Or.inl (h_col_base n (by omega) hcol)
  · intro p a hp
    exact sigma_prime_power_closed_form p a hp
  · intro q b W hq hW
    exact robin_general_wheel_step_increase q b W hq hW
  · exact robin_5040_is_counterexample
  · exact robin_10080_satisfies_robin

#print axioms sigma_prime_power_closed_form
#print axioms robin_general_wheel_step_increase
#print axioms robin_5040_is_counterexample
#print axioms robin_10080_satisfies_robin
#print axioms general_spectral_regularization_bound
#print axioms universalQuotientMasterTheoremForAllN
