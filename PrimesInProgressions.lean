import LiouvilleEnergyRH.Closure
import LiouvilleEnergyRH.Progressions.AP
import AveragedChowla

/-!
# Primes in arithmetic progressions under Hypothesis H

Hypothesis H (no Dirichlet `L`-function vanishes in `re s > 1/2`) gives, for every `η > 0`,

* `|∑_{n ≤ x} χ(n) Λ(n)| ≤ K q^η x^{1/2 + η}` for every non-principal `χ mod q`
  (`chi_psi_of_H`);
* `|φ(q) ψ(x; q, a) - x| ≤ K q^{1 + η} x^{1/2 + η}` for `a` coprime to `q` (`psiAP_of_H`,
  the prime number theorem in progressions with a power-saving, uniform error);
* the least prime `p ≡ a (mod q)` satisfies `p ≤ C q^{2 + δ}` (`least_prime_of_H`,
  Linnik's theorem with exponent `2 + δ`).
-/

namespace LiouvilleEnergyRH

open Finset

/-- Under Hypothesis H, `|∑_{n ≤ x} χ(n) Λ(n)| ≤ K q^η x^{1/2 + η}` for `χ ≠ 1`. -/
theorem chi_psi_of_H (h : HypothesisH) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Ioc 0 ⌊x⌋₊, Progressions.coef χ n‖ ≤ K * (q : ℝ) ^ η * x ^ (1 / 2 + η) :=
  Progressions.chi_psi_bound h hη

/-- **Primes in progressions.** Under Hypothesis H,
`|φ(q) ψ(x; q, a) - x| ≤ K q^{1 + η} x^{1/2 + η}`. -/
theorem psiAP_of_H (h : HypothesisH) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ x : ℝ, 1 ≤ x →
      |(q.totient : ℝ) * Progressions.psiAP q a x - x| ≤
        K * (q : ℝ) ^ (1 + η) * x ^ (1 / 2 + η) :=
  Progressions.psiAP_bound h hη

/-- **Least prime in a progression.** Under Hypothesis H, for `0 < dl ≤ 1` there is `C`
with a prime `p ≡ a (mod q)`, `p ≤ C q^{2 + dl}`, whenever `gcd(a, q) = 1`. -/
theorem least_prime_of_H (h : HypothesisH) {dl : ℝ} (hdl : 0 < dl) (hdl1 : dl ≤ 1) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ (2 + dl) :=
  Progressions.least_prime_in_AP h hdl hdl1

end LiouvilleEnergyRH
