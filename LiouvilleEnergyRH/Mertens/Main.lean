import LiouvilleEnergyRH.Hypothesis
import LiouvilleEnergyRH.Mertens.Contour
import LiouvilleEnergyRH.Mertens.ZetaBound

/-!
# The Mertens function under Hypothesis H

If `ζ(s) ≠ 0` for `re s > 1/2`, then `M(x) = ∑_{n ≤ x} μ(n) ≪_η x^{1/2 + η}` for every `η > 0`.

The function `F(s) = (s - 1) / ζ₁(s)`, with `ζ₁(s) = (s - 1) ζ(s)` continued to `ζ₁(1) = 1`,
is `1/ζ(s)` away from `s = 1` and is holomorphic on `re s > 1/2`. It equals the Dirichlet series
of `μ` on `re s > 1`. On `σ ≥ 1/2 + 8e`, `|t| > 2` the logarithmic control lemma, applied to `ζ`
with the growth bound `‖ζ(s)‖ ≤ 1/‖s - 1‖ + 1 + 2‖s‖`, gives `‖F‖ ≤ D (2 (3 + |t|)^2)^ε`; on
`|t| ≤ 2` the function `F` is bounded by compactness. The generic smoothing argument of
`LiouvilleEnergyRH.Contour.sum_bound` then bounds `M(x)`.
-/

namespace LiouvilleEnergyRH.Mertens

open Complex Set Metric Filter ArithmeticFunction Vinogradov
open scoped LSeries.notation ArithmeticFunction.Moebius

/-- `F(s) = (s - 1) / ζ₁(s)`, the holomorphic continuation of `1/ζ(s)`. -/
noncomputable def invZeta (s : ℂ) : ℂ := (s - 1) / riemannZeta₁ s

lemma zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

lemma invZeta_eq {s : ℂ} (hs : s ≠ 1) : invZeta s = (riemannZeta s)⁻¹ := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [invZeta, zeta₁_eq hs, div_mul_eq_div_div, div_self h1, one_div]

section

variable (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
include hz

lemma zeta₁_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, riemannZeta₁_one]; exact one_ne_zero
  · rw [zeta₁_eq h1]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (hz s hs h1)

lemma invZeta_differentiableAt {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ invZeta s :=
  (differentiableAt_id.sub_const 1).div differentiable_riemannZeta₁.differentiableAt
    (zeta₁_ne_zero hz hs)

end

lemma invZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) : invZeta s = LSeries ↗μ s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [invZeta_eq hs1, ← LSeries_zeta_eq_riemannZeta hs]
  exact (eq_inv_of_mul_eq_one_right (LSeries_zeta_mul_Lseries_moebius hs)).symm

lemma moebius_norm_le (n : ℕ) : ‖(↗μ : ℕ → ℂ) n‖ ≤ 1 := by
  simp only [Complex.norm_intCast]
  exact_mod_cast abs_moebius_le_one

/-- The polynomial bound for `ζ` on the disks used by the logarithmic control lemma. -/
lemma zeta_norm_on_disk {t : ℝ} (ht : 2 < |t|) {r : ℝ} (hr : r ≤ 3 / 2) {z : ℂ}
    (hzb : z ∈ ball (2 + (t : ℂ) * I) r) (hre : 1 / 2 ≤ z.re) :
    z ≠ 1 ∧ ‖riemannZeta z‖ ≤ 2 * 1 * (3 + |t|) ^ 2 := by
  have hn : ‖z - (2 + (t : ℂ) * I)‖ < r := by simpa [mem_ball, dist_eq_norm] using hzb
  have him : |z.im - t| < 3 / 2 := by
    have h := Complex.abs_im_le_norm (z - (2 + (t : ℂ) * I))
    simp at h
    linarith
  have hzim : 1 / 2 < |z.im| := by
    have := abs_sub_abs_le_abs_sub t z.im
    rw [abs_sub_comm] at this
    linarith
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hzim; simp at hzim; linarith
  refine ⟨hz1, ?_⟩
  have hd : 1 / 2 < ‖z - 1‖ := by
    have h := Complex.abs_im_le_norm (z - 1)
    simp at h
    linarith
  have hinv : 1 / ‖z - 1‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hzn := Analytic.norm_le_of_mem_ball hr hzb
  have hb := ZetaBound.norm_riemannZeta_le hre hz1
  nlinarith [abs_nonneg t]

/-- **Bound for `1/ζ` on vertical strips.** Under the zero-free half-plane `re s > 1/2`,
`‖F(σ + it)‖ ≤ D (2 (3 + |t|)^2)^ε` for `1/2 + 8e ≤ σ ≤ 2`. -/
theorem invZeta_bound (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ t : ℝ, 1 / 2 + 8 * e ≤ σ → σ ≤ 2 →
      ‖invZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := by
  obtain ⟨D₁, hD₁, hctrl⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := EulerLog.eulerLogBound) (M := 1) (ε := ε) he he'
    EulerLog.eulerLogBound_ge_one le_rfl hε
  set K : Set ℂ := Icc (1 / 2 + 8 * e) 2 ×ℂ Icc (-2) 2 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta K := by
    intro z hzK
    have hre : 1 / 2 < z.re := by
      have := (Complex.mem_reProdIm.mp hzK).1.1; linarith
    exact (invZeta_differentiableAt hz hre).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨D₁ + |B|, by positivity, ?_⟩
  intro σ t hσ hσ'
  have hbase : 1 ≤ 2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2 := by
    push_cast; nlinarith [abs_nonneg t]
  have hpow : 1 ≤ (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := Real.one_le_rpow hbase hε.le
  by_cases ht : |t| ≤ 2
  · have hmem : ((σ : ℂ) + (t : ℂ) * I) ∈ K := by
      rw [hK, Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨hσ, hσ'⟩, abs_le.mp ht⟩
    have h1 := hB _ hmem
    have h2 : B ≤ |B| := le_abs_self B
    nlinarith [abs_nonneg B]
  · push Not at ht
    have hC := OAI.SevenEighths.LogarithmicControl.conductor_height_scale_ge_exp
      ((1 : ℕ) : ℝ) t (by simp)
    obtain ⟨hEd, hEe, hEb⟩ := EulerLog.eulerLog_inner_disk (1 : DirichletCharacter ℂ 1) t
    have hLz : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq
    rw [hLz] at hEe
    have hres := hctrl (1 / 2) (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) riemannZeta
      (EulerLog.eulerLog (1 : DirichletCharacter ℂ 1)) (2 + (t : ℂ) * I) le_rfl (by norm_num) hC
      (fun z hzb => by
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hzb
        have h := zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        exact (differentiableAt_riemannZeta h.1).differentiableWithinAt)
      (fun z hzb => by
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hzb
        have h := zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        exact hz z (by linarith) h.1)
      (fun z hzb => by
        have hz2 : z ∈ ball (2 + (t : ℂ) * I) (2 - 1 / 2 - 2 * e) :=
          ball_subset_ball (by linarith) hzb
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hz2
        have h := zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        rw [Real.rpow_one]
        exact_mod_cast h.2)
      hEd hEe hEb
    have hmem := OAI.SevenEighths.LogarithmicControl.same_height_mem_disk (a := 1 / 2) (e := e)
      (t := t) (v := 8 * e) le_rfl hσ hσ'
    have hb := hres.1 _ (closedBall_subset_closedBall (by linarith) hmem)
    have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at ht; simp at ht; linarith
    rw [invZeta_eq hne]
    have hn0 := norm_nonneg (riemannZeta ((σ : ℂ) + (t : ℂ) * I))
    have hBC : 0 ≤ |B| * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := by positivity
    have hsplit : (D₁ + |B|) * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε =
        D₁ * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε +
          |B| * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := by ring
    rw [hsplit]
    have hb' : ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤
        D₁ * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := by
      have := hb
      linarith
    exact hb'.trans (le_add_of_nonneg_right hBC)

/-- **Mertens bound.** If `ζ(s) ≠ 0` for `re s > 1/2`, then for every `η > 0` there is `K` with
`‖∑_{n ≤ x} μ(n)‖ ≤ K x^{1/2 + η}` for all `x ≥ 1`. -/
theorem mertens_bound (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (↗μ : ℕ → ℂ) n‖ ≤ K * x ^ (1 / 2 + η) := by
  set e := min (η / 16) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he16 : 16 * e ≤ η := by have := min_le_left (η / 16) (1 / 2000); linarith
  have he2 : e ≤ 1 / 2000 := min_le_right _ _
  set ε := min (η / 8) (1 / 8) with hε_def
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε8 : ε ≤ 1 / 8 := min_le_right _ _
  have hεη : 8 * ε ≤ η := by have := min_le_left (η / 8) (1 / 8); linarith
  obtain ⟨D, hD, hDb⟩ := invZeta_bound hz he he' hε
  refine ⟨(1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24 + 2) *
    ((1 : ℕ) : ℝ) ^ ε, ?_⟩
  intro x hx
  have h := Contour.sum_bound (q := 1) invZeta (fun z hz' => invZeta_differentiableAt hz hz')
    ↗μ (fun z hz' => invZeta_eq_LSeries hz')
    (LSeriesSummable_moebius_iff.mpr (by simp)) moebius_norm_le hD hε hε8
    (show 1 / 2 < 1 / 2 + 8 * e by linarith) (by linarith) (by simp) hDb x hx
  have hJ0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε)) :=
    MeasureTheory.integral_nonneg (fun t => by positivity)
  have hK0 : 0 ≤ (1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24
    + 2) * ((1 : ℕ) : ℝ) ^ ε := by positivity
  have hxp : x ^ (1 / 2 + 8 * e + 4 * ε) ≤ x ^ (1 / 2 + η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  exact h.trans (mul_le_mul_of_nonneg_left hxp hK0)

end LiouvilleEnergyRH.Mertens
