-- ============================================================================
-- CONJECTURE #2 : LEHMER'S TOTIENT PROBLEM (φ(n) | n - 1) — PURE LEAN 4
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

theorem not_dvd_both_n_and_pred (n d : Nat) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (h_dvd_n : d ∣ n) (h_dvd_pred : d ∣ n - 1) : False := by
  rcases h_dvd_n with ⟨a, ha⟩
  rcases h_dvd_pred with ⟨b, hb⟩
  by_cases hab : a ≤ b
  · have h_le : d * a ≤ d * b := Nat.mul_le_mul_left d hab
    omega
  · have hba : b + 1 ≤ a := by omega
    have h_le : d * (b + 1) ≤ d * a := Nat.mul_le_mul_left d hba
    rw [Nat.mul_succ] at h_le
    omega

def IsLehmerNumber (phi : Nat → Nat) (n : Nat) : Prop :=
  2 ≤ n ∧ phi n ∣ n - 1

theorem lehmerSquarefreeObstruction
    (phi : Nat → Nat)
    (h_phi_sq : ∀ p n : Nat, 2 ≤ p → p * p ∣ n → p ∣ phi n)
    (n p : Nat) (hp : 2 ≤ p) (h_sq : p * p ∣ n) :
    ¬ IsLehmerNumber phi n := by
  rintro ⟨hn, h_lehmer⟩
  have h_p_phi : p ∣ phi n := h_phi_sq p n hp h_sq
  have h_p_pred : p ∣ n - 1 := Nat.dvd_trans h_p_phi h_lehmer
  have h_p_n : p ∣ n := Nat.dvd_trans ⟨p, rfl⟩ h_sq
  exact not_dvd_both_n_and_pred n p (by omega) hp h_p_n h_p_pred

theorem lehmerMustBeOdd
    (phi : Nat → Nat)
    (h_phi_even : ∀ n : Nat, 3 ≤ n → 2 ∣ phi n)
    (n : Nat) (hn : 3 ≤ n) (h_lehmer : IsLehmerNumber phi n) :
    n % 2 = 1 := by
  have h_2_phi : 2 ∣ phi n := h_phi_even n hn
  have h_2_pred : 2 ∣ n - 1 := Nat.dvd_trans h_2_phi h_lehmer.2
  rcases h_2_pred with ⟨k, hk⟩
  omega

def IsLehmerCandidateObstruction (n : Nat) : Prop :=
  n % 2 = 1 ∧ ∀ p : Nat, 2 ≤ p → ¬ (p * p ∣ n)

def eulerPhi (n : Nat) : Nat :=
  (List.range n).foldl (fun acc k => if Nat.gcd n (k + 1) = 1 then acc + 1 else acc) 0

theorem lehmerNoPrimeDividesPredFactor
    (phi : Nat → Nat)
    (h_phi_factors : ∀ n p q : Nat, p ∣ n → q ∣ n → p ≠ q → (p - 1) * (q - 1) ∣ phi n)
    (n p q : Nat) (hn : 2 ≤ n) (hp : 2 ≤ p) (hpq : p ≠ q)
    (hp_dvd : p ∣ n) (hq_dvd : q ∣ n)
    (h_lehmer : IsLehmerNumber phi n) :
    ¬ (p ∣ q - 1) := by
  intro hp_q1
  have h_prod_phi : (p - 1) * (q - 1) ∣ phi n := h_phi_factors n p q hp_dvd hq_dvd hpq
  have h_q1_phi : q - 1 ∣ phi n := Nat.dvd_trans ⟨p - 1, by rw [Nat.mul_comm]⟩ h_prod_phi
  have h_p_phi : p ∣ phi n := Nat.dvd_trans hp_q1 h_q1_phi
  have h_p_pred : p ∣ n - 1 := Nat.dvd_trans h_p_phi h_lehmer.2
  exact not_dvd_both_n_and_pred n p (by omega) hp hp_dvd h_p_pred

theorem lehmerNoOddSemiprime (p q : Nat) (hp : 3 ≤ p) (hq : p + 2 ≤ q) :
    ¬ ((p - 1) * (q - 1) ∣ p * q - 1) := by
  intro h_dvd
  have h_id : p * q - 1 = (p - 1) * (q - 1) + ((p - 1) + (q - 1)) := by
    have h1 : p = (p - 1) + 1 := by omega
    have h2 : q = (q - 1) + 1 := by omega
    have h_expand : ((p - 1) + 1) * ((q - 1) + 1) =
                    (p - 1) * (q - 1) + ((p - 1) + (q - 1)) + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    rw [← h1, ← h2] at h_expand
    omega
  have h_dvd_rem : (p - 1) * (q - 1) ∣ (p - 1) + (q - 1) := by
    rw [h_id] at h_dvd
    exact (Nat.dvd_add_right ⟨1, by rw [Nat.mul_one]⟩).mp h_dvd
  have h_rem_pos : 0 < (p - 1) + (q - 1) := by omega
  have h_rem_lt : (p - 1) + (q - 1) < (p - 1) * (q - 1) := by
    have hp1 : 2 ≤ p - 1 := by omega
    have hq1 : 4 ≤ q - 1 := by omega
    have h_mul : 2 * (q - 1) ≤ (p - 1) * (q - 1) := Nat.mul_le_mul_right (q - 1) hp1
    omega
  exact Nat.not_dvd_of_pos_of_lt h_rem_pos h_rem_lt h_dvd_rem

def isPrimeOrNotLehmer (n : Nat) : Bool :=
  let phi_n := eulerPhi n
  !( (n - 1) % phi_n == 0 ) || (phi_n == n - 1)

theorem lehmer_verified_up_to_500 :
    (List.range 499).all (fun k => isPrimeOrNotLehmer (k + 2)) = true := by
  decide

theorem lehmerUniversalMasterTheorem
    (phi : Nat → Nat)
    (h_phi_sq : ∀ p n : Nat, 2 ≤ p → p * p ∣ n → p ∣ phi n)
    (h_phi_even : ∀ n : Nat, 3 ≤ n → 2 ∣ phi n) :
    ∀ n : Nat, 3 ≤ n →
      ¬ IsLehmerNumber phi n ∨ IsLehmerCandidateObstruction n := by
  intro n hn
  by_cases h_lehmer : IsLehmerNumber phi n
  · right
    refine ⟨lehmerMustBeOdd phi h_phi_even n hn h_lehmer, ?_⟩
    intro p hp h_sq
    exact lehmerSquarefreeObstruction phi h_phi_sq n p hp h_sq h_lehmer
  · left
    exact h_lehmer

#print axioms not_dvd_both_n_and_pred
#print axioms lehmerSquarefreeObstruction
#print axioms lehmerNoPrimeDividesPredFactor
#print axioms lehmerNoOddSemiprime
#print axioms lehmer_verified_up_to_500
#print axioms lehmerUniversalMasterTheorem
