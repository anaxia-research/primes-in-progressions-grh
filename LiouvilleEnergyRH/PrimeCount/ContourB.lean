import LiouvilleEnergyRH.Mertens.Contour
import Vinogradov.PV.PrimeSum

/-!
# The smoothing argument with coefficients bounded by `B`

The same as `LiouvilleEnergyRH.Contour.sum_bound`, for coefficients with `‖a n‖ ≤ B` when
`n ≤ 2x`; the unsmoothing step uses `Vinogradov.PV.unsmooth`.
-/

namespace LiouvilleEnergyRH.Contour

open Complex Set Metric Filter MeasureTheory Vinogradov
open scoped LSeries.notation

theorem sum_bound_B {q : ℕ} (F : ℂ → ℂ) (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z)
    (a : ℕ → ℂ) (hFL : ∀ z : ℂ, 1 < z.re → F z = LSeries a z)
    (hsum : LSeriesSummable a ((2 : ℝ) : ℂ)) {B : ℝ} (hB0 : 0 ≤ B)
    {D ε σ₀ : ℝ} (hD : 0 ≤ D) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (hσ₀ : 1 / 2 < σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hq : (1 : ℝ) ≤ q)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (2 * q * (3 + |t|) ^ 2) ^ ε)
    (x : ℝ) (hx : 1 ≤ x) (ha : ∀ n : ℕ, (n : ℝ) ≤ 2 * x → ‖a n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤
      (1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24 + 2 * B) *
        (q : ℝ) ^ ε * x ^ (σ₀ + 4 * ε) := by
  have hx0 : 0 < x := by linarith
  set h : ℝ := x ^ σ₀ with hhdef
  have hh1 : 1 ≤ h := Real.one_le_rpow hx (by linarith)
  have hh0 : 0 < h := by linarith
  have hhx : h ≤ x := by
    calc h = x ^ σ₀ := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ₀1
      _ = x := Real.rpow_one x
  have hdiff := diff_norm_le F hFd a hFL hsum hx hh0.le hD hε hε' hσ₀ (by linarith) hB
  have hun := PV.unsmooth a hB0 hx0 hh0 (fun n hn => ha n (by linarith))
  set X : ℝ := x ^ (σ₀ + 4 * ε) with hX
  set Q : ℝ := (q : ℝ) ^ ε with hQ
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hq hε.le
  have hx4 : 1 ≤ x ^ (4 * ε) := Real.one_le_rpow hx (by linarith)
  have hXsplit : X = h * x ^ (4 * ε) := Real.rpow_add hx0 _ _
  have hhX : h ≤ X := by rw [hXsplit]; nlinarith
  have hX1 : 1 ≤ X := hh1.trans hhX
  have h18 : (18 * (q : ℝ)) ^ ε ≤ 18 * Q := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    gcongr
    calc (18 : ℝ) ^ ε ≤ 18 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 18 := Real.rpow_one 18
  have hW : (x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε)) ≤
      24 * h * X := by
    have h1 : (x + h) ^ σ₀ ≤ 2 * h := by
      calc (x + h) ^ σ₀ ≤ (2 * x) ^ σ₀ := Real.rpow_le_rpow (by linarith) (by linarith)
            (by linarith)
        _ = 2 ^ σ₀ * h := Real.mul_rpow (by norm_num) hx0.le
        _ ≤ 2 ^ (1 : ℝ) * h := by
            gcongr
            norm_num
        _ = 2 * h := by rw [Real.rpow_one]
    have h2 : (3 * h) ^ (1 - 4 * ε) ≤ 3 * h := by
      calc (3 * h) ^ (1 - 4 * ε) ≤ (3 * h) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 3 * h := Real.rpow_one _
    have h3 : (2 * (x + h)) ^ (4 * ε) ≤ 4 * x ^ (4 * ε) := by
      calc (2 * (x + h)) ^ (4 * ε) ≤ (4 * x) ^ (4 * ε) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        _ = 4 ^ (4 * ε) * x ^ (4 * ε) := Real.mul_rpow (by norm_num) hx0.le
        _ ≤ 4 ^ (1 : ℝ) * x ^ (4 * ε) := by
            gcongr
            · norm_num
            · linarith
        _ = 4 * x ^ (4 * ε) := by rw [Real.rpow_one]
    have hp2 : 0 ≤ (3 * h) ^ (1 - 4 * ε) := Real.rpow_nonneg (by linarith) _
    have hp3 : 0 ≤ (2 * (x + h)) ^ (4 * ε) := Real.rpow_nonneg (by linarith) _
    calc (x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))
        ≤ (2 * h) * ((3 * h) * (4 * x ^ (4 * ε))) := by gcongr
      _ = 24 * h * (h * x ^ (4 * ε)) := by ring
      _ ≤ 24 * h * X := by rw [hXsplit]
  set J := ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε)) with hJ
  have hstep : 1 / (2 * Real.pi) * (8 * D * (18 * q) ^ ε) * J *
      ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) ≤
      1 / (2 * Real.pi) * (8 * D * (18 * Q)) * J * (24 * h * X) := by
    gcongr
  have hun' : h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤
      ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x‖ +
        B * (h * (h + 1)) := hun
  set c := 1 / (2 * Real.pi) * (8 * D * 18) * J * 24 with hc
  have hmain : h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤ h * (c * Q * X + B * (h + 1)) := by
    calc h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖
        ≤ 1 / (2 * Real.pi) * (8 * D * (18 * Q)) * J * (24 * h * X) + B * (h * (h + 1)) := by
          linarith [hun', hdiff, hstep]
      _ = h * (c * Q * X + B * (h + 1)) := by rw [hc]; ring
  have hS := le_of_mul_le_mul_left hmain hh0
  have hQX : X ≤ Q * X := by nlinarith
  show ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤ (c + 2 * B) * Q * X
  have hBh : B * (h + 1) ≤ 2 * B * X := by nlinarith
  have hBQ : 2 * B * X ≤ 2 * B * Q * X := by
    have : 0 ≤ 2 * B * X := by positivity
    nlinarith
  nlinarith

end LiouvilleEnergyRH.Contour
