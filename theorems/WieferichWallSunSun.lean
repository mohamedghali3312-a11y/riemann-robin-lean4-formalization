/-!
  WieferichWallSunSun.lean — Lift Projectif de Wieferich & Wall–Sun–Sun en Lean 4 Pur
  - Formalisation autonome sans dépendance externe (zéro Mathlib, zéro sorryAx)
  - Caractérisation du quotient de Fermat modulo p^2 et certification bornée
  - Auteur : Mohamed Ghali (ORCID : 0009-0006-3364-5341)
-/

def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 1
  | _ + 1, _, 0, mod => 1 % mod
  | fuel + 1, base, exp, mod =>
    let half := powModAux fuel base (exp / 2) mod
    let sq := (half * half) % mod
    if exp % 2 = 0 then sq else (sq * base) % mod

def powMod (base exp mod : Nat) : Nat :=
  powModAux (exp + 1) base exp mod

def IsWieferichBase (a p : Nat) : Prop :=
  2 ≤ p ∧ powMod a (p - 1) (p * p) = 1

def fermatQuotientModP (a p : Nat) : Nat :=
  ((powMod a (p - 1) (p * p)) - 1) / p

def lucasFibModAux : Nat → Nat → Nat → Nat → Nat
  | 0, a, _, _ => a
  | n + 1, a, b, m => lucasFibModAux n (b % m) ((a + b) % m) m

def lucasFibMod (n m : Nat) : Nat × Nat :=
  (lucasFibModAux n 0 1 m, lucasFibModAux (n + 1) 0 1 m)

def IsWallSunSunPrime (p : Nat) : Prop :=
  5 ≤ p ∧ (lucasFibMod (p - 1) (p * p)).1 = 0 ∧ (lucasFibMod (p + 1) (p * p)).1 = 0

theorem wieferichProjectiveLift (a p : Nat) (h : IsWieferichBase a p) :
    powMod a (p - 1) (p * p) % p = 1 % p := by
  rcases h with ⟨_, h_eq⟩
  rw [h_eq]

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
    let r := powMod a (p - 1) (p * p)
    have h_dm := Nat.div_add_mod r p
    have h_flt' : r % p = 1 := h_flt
    rw [h_flt'] at h_dm
    have h_sub_div : (r - 1) / p = r / p := by
      have h_eq : r - 1 = p * (r / p) := by omega
      rw [h_eq, Nat.mul_div_cancel_left _ (by omega)]
    have h_q' : (r - 1) / p = 0 := h_q_zero
    rw [h_sub_div] at h_q'
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

set_option maxRecDepth 2000000 in
theorem nonWallSunSun997Certified : ¬ IsWallSunSunPrime 997 := by
  intro h
  rcases h with ⟨_, h1, _⟩
  revert h1
  decide

def isOnlyKnownWieferich (n : Nat) : Bool :=
  if powMod 2 (n - 1) (n * n) == 1 then
    (n == 1093) || (n == 3511)
  else
    true

set_option maxRecDepth 2000000 in
theorem wieferich_search_2_to_1200 :
    (List.range 1199).all (fun k => isOnlyKnownWieferich (k + 2)) = true := by
  decide

set_option maxRecDepth 2000000 in
theorem wieferich_search_1201_to_2400 :
    (List.range 1200).all (fun k => isOnlyKnownWieferich (k + 1201)) = true := by
  decide

set_option maxRecDepth 2000000 in
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
