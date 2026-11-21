import LiouvilleEnergyRH.PrimeCount.Psi

/-!
# `θ(x)` and primes in short intervals under the zero-free half-plane

* `theta_bound`: `|θ(x) - x| ≤ K x^{1/2 + η}`;
* `prime_in_short_interval`: every interval `(x, x + x^{1/2 + η}]` with `x ≥ x₀(η)` contains a
  prime, the `ε`-form of Cramér's conditional bound `p_{n+1} - p_n ≪ p_n^{1/2+ε}`.
-/

namespace LiouvilleEnergyRH.PrimeCount

open Real

lemma sqrt_mul_log_le {x η : ℝ} (hx : 1 ≤ x) (hη : 0 < η) :
    √x * Real.log x ≤ 1 / η * x ^ (1 / 2 + η) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_rpow_div hx0.le hη
  have hs : √x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hsp : 0 ≤ √x := Real.sqrt_nonneg x
  calc √x * Real.log x ≤ √x * (x ^ η / η) := mul_le_mul_of_nonneg_left hl hsp
    _ = 1 / η * (x ^ (1 / 2 : ℝ) * x ^ η) := by rw [hs]; ring
    _ = 1 / η * x ^ (1 / 2 + η) := by rw [← Real.rpow_add hx0]

/-- **`θ(x) = x + O(x^{1/2+η})`.** -/
theorem theta_bound (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |Chebyshev.theta x - x| ≤ K * x ^ (1 / 2 + η) := by
  obtain ⟨K, hK⟩ := psi_bound hz hη
  refine ⟨max K 0 + 2 / η, by positivity, fun x hx => ?_⟩
  have h1 := hK x hx
  have h2 := Chebyshev.psi_sub_theta_le hx
  have h3 := Chebyshev.theta_le_psi x
  have h4 := sqrt_mul_log_le hx hη
  have hp : 0 ≤ x ^ (1 / 2 + η) := by positivity
  have hm : K * x ^ (1 / 2 + η) ≤ max K 0 * x ^ (1 / 2 + η) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  have h5 : 2 * √x * Real.log x ≤ 2 / η * x ^ (1 / 2 + η) := by
    calc 2 * √x * Real.log x = 2 * (√x * Real.log x) := by ring
      _ ≤ 2 * (1 / η * x ^ (1 / 2 + η)) := by linarith
      _ = 2 / η * x ^ (1 / 2 + η) := by ring
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

/-- If `θ(y) > θ(x)` then some prime lies in `(x, y]`. -/
lemma exists_prime_of_theta_lt {x y : ℝ} (hx : 0 ≤ x) (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hno
  push Not at hno
  apply lt_irrefl (Chebyshev.theta x)
  have hle : Chebyshev.theta y ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
      refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
      by_contra hlt
      push Not at hlt
      have hxp : x < p := (Nat.floor_lt hx).mp hlt
      have hyp : (p : ℝ) ≤ y := by
        have hy0 : 0 ≤ y := by
          by_contra hy; push Not at hy
          have := hp.1.2
          rw [Nat.floor_of_nonpos hy.le] at this
          omega
        exact (Nat.le_floor_iff hy0).mp hp.1.2
      exact absurd (hno p hp.2 hxp) (not_lt.mpr hyp)
    · intro p hp _
      simp only [Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  linarith

/-- **Primes in short intervals (Cramér, `ε`-form).** Under the zero-free half-plane, for every
`η > 0` there is `x₀` such that every interval `(x, x + x^{1/2 + η}]` with `x ≥ x₀` contains a
prime. -/
theorem prime_in_short_interval (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ (1 / 2 + η) := by
  obtain ⟨K, hK0, hK⟩ := theta_bound hz (show 0 < η / 2 by linarith)
  set A : ℝ := 4 * (K + 1) with hA
  refine ⟨max 1 (A ^ (2 / η)), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  set h := x ^ (1 / 2 + η) with hh
  have hh0 : 0 ≤ h := by positivity
  have hhx : h ≤ x := by
    calc h ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  apply exists_prime_of_theta_lt hx0.le
  have h1 := hK x hx1
  have h2 := hK (x + h) (by linarith)
  set θ' := 1 / 2 + η / 2 with hθ'
  -- (x + h)^θ' ≤ 2 x^θ'
  have hxh : (x + h) ^ θ' ≤ 2 * x ^ θ' := by
    calc (x + h) ^ θ' ≤ (2 * x) ^ θ' := Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
      _ = 2 ^ θ' * x ^ θ' := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ θ' := by
          gcongr
          calc (2 : ℝ) ^ θ' ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  -- x^{η/2} ≥ A
  have hxA : A ≤ x ^ (η / 2) := by
    have hA0 : 0 ≤ A := by positivity
    have hx' : A ^ (2 / η) ≤ x := (le_max_right _ _).trans hx
    calc A = (A ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul hA0]; field_simp; simp
      _ ≤ x ^ (η / 2) := Real.rpow_le_rpow (by positivity) hx' (by positivity)
  have hsplit : h = x ^ θ' * x ^ (η / 2) := by
    rw [hh, ← Real.rpow_add hx0, hθ']; ring_nf
  have hpos : 0 ≤ x ^ θ' := by positivity
  have hbig : 3 * K * x ^ θ' < h := by
    rw [hsplit]
    have : 3 * K < x ^ (η / 2) := by rw [hA] at hxA; linarith
    have hxθ : 0 < x ^ θ' := by positivity
    nlinarith
  rw [abs_le] at h1 h2
  have hK2 : K * (x + h) ^ θ' ≤ 2 * K * x ^ θ' := by nlinarith
  linarith [h1.2, h2.1]

end LiouvilleEnergyRH.PrimeCount
