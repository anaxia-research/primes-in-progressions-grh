import LiouvilleEnergyRH.PrimeCount.ContourB
import LiouvilleEnergyRH.Hypothesis
import Vinogradov.Analytic

/-!
# Twisted von Mangoldt sums under Hypothesis H

For every `η > 0` there is `K` such that for every non-principal `χ` modulo `q` and `x ≥ 1`,
`‖∑_{n ≤ x} χ(n) Λ(n)‖ ≤ K q^η x^{1/2 + η}`. The function `-L'/L(s, χ)` is holomorphic on
`re s > 1/2` under Hypothesis H, equals `∑ χ(n) Λ(n) n^{-s}` on `re s > 1`, and is
`≪ log (2 q (3 + |t|)^2)` on `σ ≥ 1/2 + 8e` by `Vinogradov.Analytic.logDeriv_bound`.
-/

namespace LiouvilleEnergyRH.Progressions

open Complex Set Metric Filter ArithmeticFunction Vinogradov
open scoped LSeries.notation

/-- `-L'/L(s, χ)`. -/
noncomputable def F {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

/-- The coefficients `χ(n) Λ(n)`. -/
noncomputable def coef {q : ℕ} (χ : DirichletCharacter ℂ q) : ℕ → ℂ := ↗χ * ↗vonMangoldt

lemma F_differentiableAt (h : HypothesisH) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (F χ) s := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have hd : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    ((hL.analyticAt s).deriv).differentiableAt
  exact hd.neg.div hL.differentiableAt (h q χ s hs (Or.inl hχ))

lemma F_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    F χ s = LSeries (coef χ) s := by
  rw [F, coef, DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    ← DirichletCharacter.LFunction_eq_LSeries χ hs]

lemma coef_summable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeriesSummable (coef χ) ((2 : ℝ) : ℂ) :=
  DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simp)

lemma coef_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) (n : ℕ)
    (hn : (n : ℝ) ≤ 2 * x) : ‖coef χ n‖ ≤ Real.log (2 * x) := by
  have hL0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
  have hL : vonMangoldt n ≤ Real.log (2 * x) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp; exact Real.log_nonneg (by linarith)
    · exact vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast hpos) hn)
  simp only [coef, Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hL0]
  calc ‖χ n‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) hL0
    _ ≤ Real.log (2 * x) := by rw [one_mul]; exact hL

/-- **Twisted von Mangoldt sums under H.** -/
theorem chi_psi_bound (h : HypothesisH) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coef χ n‖ ≤ K * (q : ℝ) ^ η * x ^ (1 / 2 + η) := by
  set η' := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set e := min (η' / 32) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he32 : 32 * e ≤ η' := by have := min_le_left (η' / 32) (1 / 2000); linarith
  set ε := η' / 16 with hε_def
  have hε : 0 < ε := by positivity
  have hε8 : ε ≤ 1 / 8 := by rw [hε_def]; linarith
  set dd := η' / 4 with hdd
  have hdd0 : 0 < dd := by positivity
  obtain ⟨K₀, hK₀, hK₀b⟩ := Analytic.logDeriv_bound he he'
  set D : ℝ := K₀ / ε with hD
  have hD0 : 0 ≤ D := by positivity
  set c : ℝ := 1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24
    with hc
  have hJ0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε)) :=
    MeasureTheory.integral_nonneg (fun t => by positivity)
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c + 4 / dd, by positivity, ?_⟩
  intro q _ χ hχ x hx
  have hx0 : 0 < x := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hB : ∀ σ t : ℝ, 1 / 2 + 8 * e ≤ σ → σ ≤ 2 →
      ‖F χ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (2 * q * (3 + |t|) ^ 2) ^ ε := by
    intro σ t hσ hσ'
    have hb := hK₀b q χ hχ (1 / 2) le_rfl (by norm_num)
      (fun z hz => h q χ z (by linarith) (Or.inl hχ)) σ t hσ hσ'
    have hC1 : 1 ≤ 2 * (q : ℝ) * (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
    have hlog := Real.log_le_rpow_div (show 0 ≤ 2 * (q : ℝ) * (3 + |t|) ^ 2 by linarith) hε
    rw [F, neg_div, norm_neg]
    calc _ ≤ K₀ * Real.log (2 * q * (3 + |t|) ^ 2) := hb
      _ ≤ K₀ * ((2 * q * (3 + |t|) ^ 2) ^ ε / ε) := mul_le_mul_of_nonneg_left hlog hK₀.le
      _ = D * (2 * q * (3 + |t|) ^ 2) ^ ε := by rw [hD]; ring
  set Bx : ℝ := Real.log (2 * x) with hBx
  have hBx0 : 0 ≤ Bx := Real.log_nonneg (by linarith)
  have hs := Contour.sum_bound_B (q := q) (F χ) (fun z hz => F_differentiableAt h χ hχ hz)
    (coef χ) (fun z hz => F_eq_LSeries χ hz) (coef_summable χ) hBx0 hD0 hε hε8
    (show 1 / 2 < 1 / 2 + 8 * e by linarith) (by linarith) hq hB x hx
    (fun n hn => coef_norm_le χ hx n hn)
  have hlogx : Bx ≤ 2 / dd * x ^ dd := by
    have := Real.log_le_rpow_div (show 0 ≤ 2 * x by linarith) hdd0
    have h2 : (2 * x) ^ dd ≤ 2 * x ^ dd := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      have : (2 : ℝ) ^ dd ≤ 2 := by
        calc (2 : ℝ) ^ dd ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hdd]; linarith)
          _ = 2 := Real.rpow_one 2
      nlinarith [Real.rpow_nonneg hx0.le dd]
    calc Bx ≤ (2 * x) ^ dd / dd := this
      _ ≤ 2 * x ^ dd / dd := by gcongr
      _ = 2 / dd * x ^ dd := by ring
  have hxdd : 1 ≤ x ^ dd := Real.one_le_rpow hx hdd0.le
  have hX : x ^ (1 / 2 + 8 * e + 4 * ε) ≤ x ^ (1 / 2 + η' - dd) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [hε_def, hdd]; linarith)
  have hsplit : x ^ (1 / 2 + η' - dd) * x ^ dd = x ^ (1 / 2 + η') := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hqε : (q : ℝ) ^ ε ≤ (q : ℝ) ^ η := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hxη : x ^ (1 / 2 + η') ≤ x ^ (1 / 2 + η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hcoef : c + 2 * Bx ≤ (c + 4 / dd) * x ^ dd := by
    have ha : c ≤ c * x ^ dd := le_mul_of_one_le_right hc0 hxdd
    have : 2 * Bx ≤ 4 / dd * x ^ dd := by
      have : 2 * (2 / dd * x ^ dd) = 4 / dd * x ^ dd := by ring
      linarith
    nlinarith
  have hp1 : 0 ≤ (q : ℝ) ^ ε := by positivity
  have hp2 : 0 ≤ x ^ (1 / 2 + η' - dd) := by positivity
  calc ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coef χ n‖
      ≤ (c + 2 * Bx) * (q : ℝ) ^ ε * x ^ (1 / 2 + 8 * e + 4 * ε) := hs
    _ ≤ ((c + 4 / dd) * x ^ dd) * (q : ℝ) ^ η * x ^ (1 / 2 + η' - dd) := by gcongr
    _ = (c + 4 / dd) * (q : ℝ) ^ η * (x ^ (1 / 2 + η' - dd) * x ^ dd) := by ring
    _ = (c + 4 / dd) * (q : ℝ) ^ η * x ^ (1 / 2 + η') := by rw [hsplit]
    _ ≤ (c + 4 / dd) * (q : ℝ) ^ η * x ^ (1 / 2 + η) := by gcongr

end LiouvilleEnergyRH.Progressions
