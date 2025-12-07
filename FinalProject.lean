import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Quotient
import Mathlib.Tactic.Ring
import Mathlib.Tactic

open Nat

lemma prime_dvd_mul {p a b : ℕ} (hp : p.Prime) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

lemma prime_not_dvd_mul {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b := by
  intro h
  cases prime_dvd_mul hp h with
  | inl h' => contradiction
  | inr h' => contradiction

lemma prime_dvd_factorial (p : ℕ) (hp : p.Prime) : p ∣ p ! :=
  have h1 : 0 < p := by
    apply hp.pos
  have h2 : p <= p := by
    rfl
  dvd_factorial h1 h2

lemma prime_not_dvd_factorial_of_lt {p k : ℕ} (hp : p.Prime) (hk : k < p) : ¬ p ∣ k ! := by
  intro h
  have h1 : p <= k := by
    apply hp.dvd_factorial.mp h -- if a divides b!, then a is less than or equal to b
  have h2 : ¬ k < p := by
    apply not_lt_of_ge h1
  contradiction

lemma prime_dvd_choose {p k : ℕ} (hp : p.Prime) (hk : 0 < k) (hk' : k < p) : p ∣ choose p k := by
    have h_eq : choose p k * k ! * (p - k)! = p ! := by
      exact choose_mul_factorial_mul_factorial (le_of_lt hk')
    have hp_dvd : p ∣ p ! := by
      apply prime_dvd_factorial p hp
    have h_eq_backwards : p ! = choose p k * k ! * (p - k)! := by
      rw [h_eq]
    rw [h_eq_backwards] at hp_dvd
    have not_p_dvd_k! : ¬ p ∣ k ! := by
      apply prime_not_dvd_factorial_of_lt hp hk'
    have p_minus_k_lt_p : p - k < p := by
      apply sub_lt
      · apply hp.pos
      · exact hk
    have not_p_dvd_p_minus_k! : ¬ p ∣ (p - k) ! := by
      apply prime_not_dvd_factorial_of_lt hp p_minus_k_lt_p
    rw [mul_assoc] at hp_dvd
    cases prime_dvd_mul hp hp_dvd with
    | inl h =>
      exact h
    | inr h =>
      cases prime_dvd_mul hp h with
      | inl h' =>
        contradiction
      | inr h' =>
        contradiction

lemma nat_cast_eq_zero_of_dvd {p n : ℕ} (h : p ∣ n) : (n : ZMod p) = 0 := by -- if p, a prime, divides n, then n mod p is 0
  simp [ZMod.nat_cast_zmod_eq_zero_iff_dvd]
  exact h

lemma freshman_dream {p : ℕ} (hp : p.Prime) (a b : ZMod p) : (a + b) ^ p = a ^ p + b ^ p := by
  rw [add_pow]

  have middle_zero : ∀ m ∈ Finset.range (p + 1), 0 < m → m < p → a ^ m * b ^ (p - m) * (choose p m : ZMod p) = 0 := by
    intro m _ hm0 hmp
    have hdvd : p ∣ choose p m := prime_dvd_choose hp hm0 hmp -- use previous lemma
    have h1 : (choose p m : ZMod p) = 0 := by
      apply nat_cast_eq_zero_of_dvd
      exact hdvd
    rw [h1]
    simp

  have h : Finset.sum (Finset.range (p + 1)) (fun m => a ^ m * b ^ (p - m) * ↑(choose p m)) = a ^ 0 * b ^ p * ↑(choose p 0) + a ^ p * b ^ 0 * ↑(choose p p) := by
    have : ∀ m ∈ Finset.range (p + 1), m ≠ 0 → m ≠ p → a ^ m * b ^ (p - m) * ↑(choose p m) = 0 := by
      intro m hm hm0 hmp
      apply middle_zero m hm
      · apply Nat.pos_iff_ne_zero.mpr hm0
      · have : m < p + 1 := Finset.mem_range.mp hm
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ this) with
        | inl h =>
          exact h
        | inr h =>
          contradiction
    have h0 : 0 ∈ Finset.range (p + 1) := by simp [hp.pos]
    have hp_mem : p ∈ Finset.range (p + 1) := by simp
    rw [← Finset.sum_erase_add _ _ h0]
    simp only [Nat.pow_zero, Nat.sub_zero, choose_zero_right]
    have hp_in_erase : p ∈ (Finset.range (p + 1)).erase 0 := by
      simp [Finset.mem_erase]
      apply Nat.ne_of_gt
      exact hp.pos
    rw [← Finset.sum_erase_add _ _ hp_in_erase]
    rw [Nat.sub_self]
    simp [Nat.pow_zero]
    rw [add_comm]
    suffices Finset.sum (((Finset.range (p + 1)).erase 0).erase p) (fun m => a ^ m * b ^ (p - m) * ↑(choose p m)) = 0 by
      simp [this]
    apply Finset.sum_eq_zero
    intro m hm
    simp [Finset.mem_erase] at hm
    obtain ⟨h1, h2, h3⟩ := hm
    apply this
    · apply Finset.mem_range.mpr
      exact h3
    · exact h2
    · exact h1
  rw [h]
  simp [choose_zero_right, choose_self]
  rw [add_comm]

theorem fermat_little_theorem {p : ℕ} (hp : p.Prime) (a : ℕ) : (a : ZMod p) ^ p = a := by
  induction a with
  | zero =>
    simp
    rw [zero_pow]
    exact hp.pos
  | succ n ih =>
    have dream : ((n : ZMod p) + 1) ^ p = (n : ZMod p) ^ p + 1 ^ p := freshman_dream hp (n : ZMod p) 1
    simp only [Nat.cast_succ]
    rw [dream]
    rw [ih]
    rw [one_pow]
