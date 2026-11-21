/-
The square kernel `λ * 1` of the Liouville function.

We show that `σ := λ * 1` takes only the values `0` and `1`, and that it
vanishes off the perfect squares.  This is the arithmetic input behind the
identity `λ = σ * μ`, i.e. `λ(n) = ∑_{d² ∣ n} μ(n / d²)`.
-/
import Mathlib

open ArithmeticFunction Finset

namespace ChowlaRH

/-- The square kernel `σ = λ * 1`. -/
def sqKernel : ArithmeticFunction ℤ := liouville * (zeta : ArithmeticFunction ℤ)

theorem sqKernel_isMultiplicative : sqKernel.IsMultiplicative :=
  isMultiplicative_liouville.mul isMultiplicative_zeta.natCast

/-- The alternating sum `∑_{i ≤ k} (-1)^i`. -/
theorem alt_sum (k : ℕ) :
    (∑ i ∈ range (k + 1), ((-1 : ℤ) ^ i)) = if Even k then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using hk
      simp [hk, this, (hk.add_one).neg_one_pow]
    · have h1 : Even (k + 1) := hk.add_one
      have : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h1, this, h1.neg_one_pow]

theorem sqKernel_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sqKernel (p ^ k) = if Even k then 1 else 0 := by
  rw [sqKernel, coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp, ← alt_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp]

/-- `σ(n) ∈ {0, 1}` and `σ(n) ≠ 0` forces `n` to be a square. -/
theorem sqKernel_spec (n : ℕ) :
    (sqKernel n = 0 ∨ sqKernel n = 1) ∧ (sqKernel n ≠ 0 → IsSquare n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ =>
    rw [sqKernel_prime_pow hp]
    refine ⟨by split_ifs <;> simp, fun h => ?_⟩
    split_ifs at h with hk
    · obtain ⟨r, rfl⟩ := hk
      exact ⟨p ^ r, by rw [pow_add]⟩
    · exact absurd rfl h
  | zero => simp
  | one => simp [sqKernel_isMultiplicative.map_one]
  | coprime a b _ _ hab iha ihb =>
    rw [sqKernel_isMultiplicative.map_mul_of_coprime hab]
    refine ⟨?_, fun h => ?_⟩
    · rcases iha.1 with h1 | h1 <;> rcases ihb.1 with h2 | h2 <;> simp [h1, h2]
    · have ha : sqKernel a ≠ 0 := left_ne_zero_of_mul h
      have hb : sqKernel b ≠ 0 := right_ne_zero_of_mul h
      obtain ⟨r, hr⟩ := iha.2 ha
      obtain ⟨s, hs⟩ := ihb.2 hb
      exact ⟨r * s, by rw [hr, hs]; ring⟩

/-- `σ(d²) = 1` for `d ≥ 1`, so `σ` is exactly the indicator of the nonzero squares. -/
theorem sqKernel_sq {d : ℕ} (hd : d ≠ 0) : sqKernel (d * d) = 1 := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ =>
    rw [← pow_add, sqKernel_prime_pow hp]; simp
  | zero => exact absurd rfl hd
  | one => simp [sqKernel_isMultiplicative.map_one]
  | coprime a b ha hb hab iha ihb =>
    have : a * b * (a * b) = (a * a) * (b * b) := by ring
    have hc : Nat.Coprime (a * a) (b * b) := by simpa [pow_two] using Nat.Coprime.pow 2 2 hab
    rw [this, sqKernel_isMultiplicative.map_mul_of_coprime hc,
      iha (by omega), ihb (by omega), one_mul]

/-- The convolution identity `λ = σ * μ`. -/
theorem liouville_eq_sqKernel_mul_moebius :
    liouville = sqKernel * (moebius : ArithmeticFunction ℤ) := by
  rw [sqKernel, mul_assoc, coe_zeta_mul_moebius, mul_one]

/-- Divisor-sum form: `∑_{d ∣ n} λ(d) = σ(n)`, which is `1` on squares and `0` otherwise. -/
theorem sum_divisors_liouville (n : ℕ) :
    ∑ d ∈ n.divisors, liouville d = sqKernel n := by
  rw [sqKernel, coe_mul_zeta_apply]

end ChowlaRH
