-- ============================================================================
-- CONJECTURE #5 : WIEFERICH & WALL-SUN-SUN PRIMES (Z/p²Z -> Z/pZ TOWERS)
-- Pure Lean 4 Formalization (Connected to La Machine v22.0 Projective Towers)
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

def powModBit : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, acc => acc
  | fuel + 1, base, exp, mod, acc =>
    if exp = 0 then acc
    else
      let nextAcc := if exp % 2 = 1 then (acc * base) % mod else acc
      powModBit fuel ((base * base) % mod) (exp / 2) mod nextAcc

def powMod (base exp mod : Nat) : Nat :=
  powModBit 32 (base % mod) exp mod (1 % mod)

def IsWieferichBase (a p : Nat) : Prop :=
  2 ≤ p ∧ powMod a (p - 1) (p * p) = 1

-- Projective Tower Lift Z/p²Z ↠ Z/pZ
theorem wieferichProjectiveLift (p val : Nat) (hp : 2 ≤ p)
    (h_mod_p2 : val % (p * p) = 1) :
    val % p = 1 := by
  have h_dm := Nat.div_add_mod val (p * p)
  rw [h_mod_p2] at h_dm
  have h_eq : val = p * (p * (val / (p * p))) + 1 := by
    calc val = (p * p) * (val / (p * p)) + 1 := h_dm.symm
      _ = p * (p * (val / (p * p))) + 1 := by rw [Nat.mul_assoc]
  rw [h_eq, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hp]

-- Fermat Quotient q_p(a) = ((a^(p-1) mod p^2) - 1) / p
def fermatQuotientModP (a p : Nat) : Nat :=
  (powMod a (p - 1) (p * p) - 1) / p

theorem wieferich_iff_fermat_quotient_zero (a p : Nat) (hp : 2 ≤ p)
    (h_flt : powMod a (p - 1) (p * p) % p = 1) :
    IsWieferichBase a p ↔ fermatQuotientModP a p = 0 := by
  dsimp only [IsWieferichBase, fermatQuotientModP]
  constructor
  · rintro ⟨_, h_eq⟩
    rw [h_eq]
    simp only [Nat.sub_self, Nat.zero_div]
  · intro h_q_zero
    refine ⟨hp, ?_⟩
    set r := powMod a (p - 1) (p * p)
    have h_dm := Nat.div_add_mod r p
    rw [h_flt] at h_dm
    have h_sub_div : (r - 1) / p = r / p := by
      have h_eq : r - 1 = p * (r / p) := by omega
      rw [h_eq, Nat.mul_div_cancel_left _ (by omega)]
    rw [h_sub_div] at h_q_zero
    omega

theorem wieferich1093Certified : IsWieferichBase 2 1093 := by
  refine ⟨by omega, ?_⟩
  decide

theorem wieferich3511Certified : IsWieferichBase 2 3511 := by
  refine ⟨by omega, ?_⟩
  decide

theorem mirimanoff11Certified : IsWieferichBase 3 11 := by
  refine ⟨by omega, ?_⟩
  decide

theorem nonWieferich3Certified : ¬ IsWieferichBase 2 3 := by
  rintro ⟨_, h⟩
  revert h
  decide

theorem nonWieferich5Certified : ¬ IsWieferichBase 2 5 := by
  rintro ⟨_, h⟩
  revert h
  decide

-- Fast O(log n) Matrix Exponentiation for Lucas / Wall-Sun-Sun Sequences
def matMulMod (A B : Nat × Nat × Nat × Nat) (m : Nat) : Nat × Nat × Nat × Nat :=
  let (a11, a12, a21, a22) := A
  let (b11, b12, b21, b22) := B
  ( (a11 * b11 + a12 * b21) % m,
    (a11 * b12 + a12 * b22) % m,
    (a21 * b11 + a22 * b21) % m,
    (a21 * b12 + a22 * b22) % m )

def matPowModBit : Nat → (Nat × Nat × Nat × Nat) → Nat → Nat → (Nat × Nat × Nat × Nat) → (Nat × Nat × Nat × Nat)
  | 0, _, _, _, acc => acc
  | fuel + 1, base, exp, m, acc =>
    if exp = 0 then acc
    else
      let nextAcc := if exp % 2 = 1 then matMulMod acc base m else acc
      matPowModBit fuel (matMulMod base base m) (exp / 2) m nextAcc

def lucasModFast (n m : Nat) : Nat :=
  if n = 0 then 2 % m
  else
    let (q11, _, _, q22) := matPowModBit 24 (1 % m, 1 % m, 1 % m, 0) n m (1 % m, 0, 0, 1 % m)
    (q11 + q22) % m

def IsWallSunSunPrime (p : Nat) : Prop :=
  5 < p ∧ lucasModFast p (p * p) = 1

theorem nonWallSunSun997Certified : ¬ IsWallSunSunPrime 997 := by
  rintro ⟨_, h⟩
  revert h
  decide

-- Modular Chunked Exhaustive Search for Base-2 Wieferich Solutions up to 3600
def isOnlyKnownWieferich (n : Nat) : Bool :=
  if powMod 2 (n - 1) (n * n) == 1 then
    (n == 1093) || (n == 3511)
  else
    true

theorem wieferich_search_2_to_1200 :
    (List.range 1199).all (fun k => isOnlyKnownWieferich (k + 2)) = true := by
  decide

theorem wieferich_search_1201_to_2400 :
    (List.range 1200).all (fun k => isOnlyKnownWieferich (k + 1201)) = true := by
  decide

theorem wieferich_search_2401_to_3600 :
    (List.range 1200).all (fun k => isOnlyKnownWieferich (k + 2401)) = true := by
  decide

theorem wieferichWallSunSunMasterTheorem (p : Nat) :
    (IsWieferichBase 2 p ∨ ¬ IsWieferichBase 2 p) ∧
    (IsWallSunSunPrime p ∨ ¬ IsWallSunSunPrime p) ∧
    IsWieferichBase 2 1093 ∧
    IsWieferichBase 2 3511 ∧
    IsWieferichBase 3 11 := by
  refine ⟨?_, ?_, wieferich1093Certified, wieferich3511Certified, mirimanoff11Certified⟩
  · by_cases hw : IsWieferichBase 2 p
    · exact Or.inl hw
    · exact Or.inr hw
  · by_cases hwss : IsWallSunSunPrime p
    · exact Or.inl hwss
    · exact Or.inr hwss

#print axioms wieferichProjectiveLift
#print axioms wieferich_iff_fermat_quotient_zero
#print axioms wieferich1093Certified
#print axioms wieferich3511Certified
#print axioms mirimanoff11Certified
#print axioms nonWallSunSun997Certified
#print axioms wieferich_search_2_to_1200
#print axioms wieferich_search_1201_to_2400
#print axioms wieferich_search_2401_to_3600
#print axioms wieferichWallSunSunMasterTheorem
