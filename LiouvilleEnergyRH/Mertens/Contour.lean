import Vinogradov.CharacterSums

/-!
# Partial sums of Dirichlet series from bounds on a vertical strip

A generic form of the smoothing argument of `Vinogradov.CharacterSums`: a Dirichlet series with
coefficients of norm at most `1`, continued holomorphically to `re s > 1/2` and polynomially
bounded with exponent `2ε` on `σ₀ ≤ re s ≤ 2`, has partial sums `≪ x^{σ₀ + 4ε}`.
-/

namespace LiouvilleEnergyRH.Contour

open Complex Set Metric Filter MeasureTheory Vinogradov
open scoped LSeries.notation


theorem scale_le (q : ℕ) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (2 * q * (3 + |t|) ^ 2) ^ ε ≤ (18 * q) ^ ε * (1 + |t|) ^ (2 * ε) := by
  have h0 : (3 + |t|) ^ 2 ≤ 9 * (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : 2 * (q : ℝ) * (3 + |t|) ^ 2 ≤ 18 * q * (1 + |t|) ^ 2 := by nlinarith
  calc (2 * q * (3 + |t|) ^ 2) ^ ε ≤ (18 * q * (1 + |t|) ^ 2) ^ ε :=
        Real.rpow_le_rpow (by positivity) h1 hε
    _ = (18 * q) ^ ε * (1 + |t|) ^ (2 * ε) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_two,
          ← Real.rpow_mul (by positivity)]

/-- The integrand `x^z L(z, χ) / (z (z + 1))`. -/
noncomputable def integrand (F : ℂ → ℂ) (x : ℝ) (z : ℂ) :
    ℂ :=
  ((1 / x : ℝ) : ℂ) ^ (-z) * (F z / (z * (z + 1)))

theorem integrand_differentiableAt (F : ℂ → ℂ)
    (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z) {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    DifferentiableAt ℂ (integrand F x) z := by
  have hc : ((1 / x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (one_div_pos.mpr hx).ne'
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; norm_num at hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have h' : (z + 1).re = 0 := by rw [h]; simp
    simp at h'
    linarith
  change DifferentiableAt ℂ (fun w => ((1 / x : ℝ) : ℂ) ^ (-w) *
    (F w / (w * (w + 1)))) z
  apply DifferentiableAt.mul
  · exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hc)
  · exact (hFd z hz).div (differentiableAt_id.mul (differentiableAt_id.add_const 1))
      (mul_ne_zero hz0 hz1)

/-- `‖L(s, χ) / (s (s + 1))‖ ≤ 8 D (18 q)^ε (1 + |t|)^{-(2 - 2ε)}`. -/
theorem quotient_norm_le {q : ℕ} (F : ℂ → ℂ) {D ε σ t : ℝ}
    (hσ : 1 / 2 ≤ σ) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hB : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ‖F ((σ : ℂ) + (t : ℂ) * I) /
        (((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1))‖ ≤
      8 * D * (18 * q) ^ ε * (1 + |t|) ^ (-(2 - 2 * ε)) := by
  have ht : 0 < 1 + |t| := by positivity
  have hden := Analytic.denominator_ge (t := t) hσ
  have hsplit : (1 + |t|) ^ (-(2 - 2 * ε)) = (1 + |t|) ^ (2 * ε) / (1 + |t|) ^ 2 := by
    rw [show -(2 - 2 * ε) = 2 * ε - 2 by ring, Real.rpow_sub ht, Real.rpow_two]
  have hL := hB.trans (mul_le_mul_of_nonneg_left (scale_le q t hε) hD)
  rw [norm_div, hsplit]
  calc ‖F ((σ : ℂ) + (t : ℂ) * I)‖ /
        ‖((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1)‖
      ≤ D * ((18 * q) ^ ε * (1 + |t|) ^ (2 * ε)) / ((1 + |t|) ^ 2 / 8) := by
        gcongr
    _ = 8 * D * (18 * q) ^ ε * ((1 + |t|) ^ (2 * ε) / (1 + |t|) ^ 2) := by
        field_simp

theorem integrand_norm_le {q : ℕ} (F : ℂ → ℂ) {x D ε : ℝ}
    (hx : 0 < x) {σ t : ℝ} (hσ : 1 / 2 ≤ σ) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hB : ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ‖integrand F x ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      8 * D * (18 * q) ^ ε * x ^ σ * (1 + |t|) ^ (-(2 - 2 * ε)) := by
  have hpow : ‖((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
  unfold integrand
  rw [norm_mul, hpow]
  have h := quotient_norm_le F hσ hD hε hB
  have hxσ : 0 ≤ x ^ σ := by positivity
  calc x ^ σ * ‖F ((σ : ℂ) + (t : ℂ) * I) /
        (((σ : ℂ) + (t : ℂ) * I) * ((σ : ℂ) + (t : ℂ) * I + 1))‖
      ≤ x ^ σ * (8 * D * (18 * q) ^ ε * (1 + |t|) ^ (-(2 - 2 * ε))) := by gcongr
    _ = _ := by ring

/-- The Riesz mean of `χ` as an integral over the line `re s = σ₀`. -/
theorem rieszSum_eq_line {q : ℕ} (F : ℂ → ℂ) (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z)
    (a : ℕ → ℂ) (hFL : ∀ z : ℂ, 1 < z.re → F z = LSeries a z)
    (hsum : LSeriesSummable a ((2 : ℝ) : ℂ)) {x D ε σ₀ : ℝ} (hx : 1 ≤ x) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε' : ε < 1 / 2)
    (hσ₀ : 1 / 2 < σ₀) (hσ₀' : σ₀ ≤ 2)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    Riesz.rieszSum a x =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, integrand F x ((σ₀ : ℂ) + (t : ℂ) * I) := by
  have hx0 : 0 < x := by linarith
  have hI : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 - 2 * ε))) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2 - 2 * ε)
      (by rw [Module.finrank_self]; push_cast; linarith)
    simpa only [Real.norm_eq_abs] using h
  set c : ℝ := 8 * D * (18 * q) ^ ε with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 → ∀ t : ℝ,
      ‖integrand F x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ c * x ^ σ * (1 + |t|) ^ (-(2 - 2 * ε)) :=
    fun σ h1 h2 t => integrand_norm_le F hx0 (by linarith) hD hε (hB σ t h1 h2)
  have hdiff : ∀ z : ℂ, σ₀ ≤ z.re → z.re ≤ 2 → DifferentiableAt ℂ (integrand F x) z :=
    fun z h1 _ => integrand_differentiableAt F hFd hx0 (by linarith)
  have hcont : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      Continuous (fun t : ℝ => integrand F x ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h1 h2
    rw [continuous_iff_continuousAt]
    intro t
    apply ContinuousAt.comp (g := integrand F x)
    · exact (hdiff _ (by simpa using h1) (by simpa using h2)).continuousAt
    · fun_prop
  have hint : ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      Integrable (fun t : ℝ => integrand F x ((σ : ℂ) + (t : ℂ) * I)) := by
    intro σ h1 h2
    refine Integrable.mono' (hI.const_mul (c * x ^ σ))
      (hcont σ h1 h2).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun t => by simpa [mul_assoc] using hpt σ h1 h2 t)
  have hgrowth : ∀ σ ∈ Icc σ₀ 2, ∀ t : ℝ,
      ‖integrand F x ((σ : ℂ) + (t : ℂ) * I)‖ ≤ (c * x ^ (2 : ℝ)) * Real.exp (0 * |t|) := by
    intro σ hσ t
    rw [zero_mul, Real.exp_zero, mul_one]
    refine (hpt σ hσ.1 hσ.2 t).trans ?_
    have h1 : x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have h2 : (1 + |t|) ^ (-(2 - 2 * ε)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
    have h4 : 0 ≤ (1 + |t|) ^ (-(2 - 2 * ε)) := by positivity
    calc c * x ^ σ * (1 + |t|) ^ (-(2 - 2 * ε)) ≤ c * x ^ (2 : ℝ) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 h4 (by positivity)
      _ = _ := by ring
  have hshift := ContourShift.integral_eq_of_exponential_strip_growth (integrand F x) σ₀ 2 0
    (c * x ^ (2 : ℝ)) hσ₀' le_rfl (by positivity) hdiff
    (hint σ₀ le_rfl hσ₀') (hint 2 hσ₀' le_rfl) hgrowth
  have hR := Riesz.rieszSum_mellinInv (σ := 2) (by norm_num) hx0 a hsum
  have hline : mellinInv 2 (fun s => LSeries a s / (s * (s + 1))) (1 / x) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, integrand F x (((2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall (fun t => ?_)
    have hre : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * I).re := by simp
    simp only [integrand, smul_eq_mul]
    rw [← hFL _ hre]
  rw [← hR, hline, ← hshift]


theorem integrable_decay {r : ℝ} (hr : 1 < r) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-r)) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r)
    (by rw [Module.finrank_self]; push_cast; linarith)
  simpa only [Real.norm_eq_abs] using h

theorem integrand_integrable {q : ℕ} (F : ℂ → ℂ) (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z)
    {x D ε σ : ℝ} (hx : 0 < x) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε' : ε < 1 / 2) (hσ : 1 / 2 < σ)
    (hB : ∀ t : ℝ, ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    Integrable (fun t : ℝ => integrand F x ((σ : ℂ) + (t : ℂ) * I)) := by
  have hI := integrable_decay (r := 2 - 2 * ε) (by linarith)
  have hcont : Continuous (fun t : ℝ => integrand F x ((σ : ℂ) + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    apply ContinuousAt.comp (g := integrand F x)
    · exact (integrand_differentiableAt F hFd hx (by simp; linarith)).continuousAt
    · fun_prop
  refine Integrable.mono' (hI.const_mul (8 * D * (18 * q) ^ ε * x ^ σ))
    hcont.aestronglyMeasurable ?_
  exact Eventually.of_forall (fun t => integrand_norm_le F hx hσ.le hD hε (hB t))

/-- `y · x^{-z}`-form of the integrand: `y · integrand = y^{z+1} L(z) / (z (z + 1))`. -/
theorem ofReal_mul_integrand (F : ℂ → ℂ) {y : ℝ}
    (hy : 0 < y) (z : ℂ) :
    (y : ℂ) * integrand F y z =
      (y : ℂ) ^ (z + 1) * (F z / (z * (z + 1))) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hy1 : ((1 / y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (one_div_pos.mpr hy).ne'
  have h1 : ((1 / y : ℝ) : ℂ) ^ (-z) = (y : ℂ) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hy1, Complex.cpow_def_of_ne_zero hy0,
      ← Complex.ofReal_log (one_div_pos.mpr hy).le, ← Complex.ofReal_log hy.le, one_div,
      Real.log_inv]
    push_cast
    congr 1
    ring
  unfold integrand
  rw [h1, Complex.cpow_add _ _ hy0, Complex.cpow_one]
  ring

/-- The difference of two Riesz means as an integral over the line `re s = σ₀`. -/
theorem diff_eq_line {q : ℕ} (F : ℂ → ℂ) (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z)
    (a : ℕ → ℂ) (hFL : ∀ z : ℂ, 1 < z.re → F z = LSeries a z)
    (hsum : LSeriesSummable a ((2 : ℝ) : ℂ)) {x h D ε σ₀ : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hε' : ε < 1 / 2)
    (hσ₀ : 1 / 2 < σ₀) (hσ₀' : σ₀ ≤ 2)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
          (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)) *
        (F ((σ₀ : ℂ) + (t : ℂ) * I) /
          (((σ₀ : ℂ) + (t : ℂ) * I) * ((σ₀ : ℂ) + (t : ℂ) * I + 1))) := by
  have hx0 : 0 < x := by linarith
  have hxh : 0 < x + h := by linarith
  have hI1 := integrand_integrable F hFd hxh hD hε hε' hσ₀ (fun t => hB σ₀ t le_rfl hσ₀')
  have hI2 := integrand_integrable F hFd hx0 hD hε hε' hσ₀ (fun t => hB σ₀ t le_rfl hσ₀')
  rw [rieszSum_eq_line F hFd a hFL hsum (show 1 ≤ x + h by linarith) hD hε hε' hσ₀ hσ₀' hB,
    rieszSum_eq_line F hFd a hFL hsum hx hD hε hε' hσ₀ hσ₀' hB, mul_smul_comm, mul_smul_comm, ← smul_sub,
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (hI1.const_mul _)
      (hI2.const_mul _)]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall (fun t => ?_)
  dsimp only
  rw [ofReal_mul_integrand F hxh, ofReal_mul_integrand F hx0]
  ring

/-- `‖(x + h)^w - x^w‖ ≤ ‖w‖ (x + h)^σ h` for `re w = σ + 1`, `σ ≥ 0`. -/
theorem cpow_sub_norm_le {x h σ : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hσ : 0 ≤ σ) {w : ℂ}
    (hw : w.re = σ + 1) :
    ‖((x + h : ℝ) : ℂ) ^ w - (x : ℂ) ^ w‖ ≤ ‖w‖ * (x + h) ^ σ * h := by
  have hderiv : ∀ u ∈ Icc x (x + h), HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ w)
      (w * (u : ℂ) ^ (w - 1)) (Icc x (x + h)) u := by
    intro u hu
    have hu0 : 0 < u := hx.trans_le hu.1
    exact ((Complex.hasStrictDerivAt_cpow_const
      (Complex.ofReal_mem_slitPlane.mpr hu0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ u ∈ Ico x (x + h), ‖w * (u : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * (x + h) ^ σ := by
    intro u hu
    have hu0 : 0 < u := hx.trans_le hu.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (w - 1).re = σ := by simp [hw]
    rw [hre]
    gcongr
    exact hu.2.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (x + h)
    ⟨by linarith, le_rfl⟩
  simpa using this

/-- `‖(x + h)^w - x^w‖ ≤ 2 (x + h)^{σ + 1}` for `re w = σ + 1`, `σ ≥ 0`. -/
theorem cpow_sub_norm_le' {x h σ : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hσ : 0 ≤ σ) {w : ℂ}
    (hw : w.re = σ + 1) :
    ‖((x + h : ℝ) : ℂ) ^ w - (x : ℂ) ^ w‖ ≤ 2 * (x + h) ^ (σ + 1) := by
  have hxh : 0 < x + h := by linarith
  have hm : x ^ (σ + 1) ≤ (x + h) ^ (σ + 1) :=
    Real.rpow_le_rpow hx.le (by linarith) (by linarith)
  calc _ ≤ ‖((x + h : ℝ) : ℂ) ^ w‖ + ‖(x : ℂ) ^ w‖ := norm_sub_le _ _
    _ = (x + h) ^ (σ + 1) + x ^ (σ + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxh, Complex.norm_cpow_eq_rpow_re_of_pos hx, hw]
    _ ≤ 2 * (x + h) ^ (σ + 1) := by linarith

/-- If `N ≤ M a` and `N ≤ M b`, then `N ≤ M a^{1-θ} b^θ`. -/
theorem le_interp {N M a b θ : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : N ≤ M * a) (h2 : N ≤ M * b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    N ≤ M * (a ^ (1 - θ) * b ^ θ) := by
  have hs : (1 - θ) + θ = 1 := by ring
  have hpow : ∀ y : ℝ, 0 ≤ y → y ^ (1 - θ) * y ^ θ = y := fun y hy => by
    rw [← Real.rpow_add' hy (by rw [hs]; norm_num), hs, Real.rpow_one]
  calc N = N ^ (1 - θ) * N ^ θ := (hpow N hN).symm
    _ ≤ (M * a) ^ (1 - θ) * (M * b) ^ θ :=
        mul_le_mul (Real.rpow_le_rpow hN h1 (by linarith)) (Real.rpow_le_rpow hN h2 hθ0)
          (by positivity) (Real.rpow_nonneg (hN.trans h1) _)
    _ = (M ^ (1 - θ) * M ^ θ) * (a ^ (1 - θ) * b ^ θ) := by
        rw [Real.mul_rpow hM ha, Real.mul_rpow hM hb]; ring
    _ = M * (a ^ (1 - θ) * b ^ θ) := by rw [hpow M hM]

/-- The bound for the difference of two Riesz means. -/
theorem diff_norm_le {q : ℕ} (F : ℂ → ℂ) (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z)
    (a : ℕ → ℂ) (hFL : ∀ z : ℂ, 1 < z.re → F z = LSeries a z)
    (hsum : LSeriesSummable a ((2 : ℝ) : ℂ)) {x h D ε σ₀ : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h) (hD : 0 ≤ D) (hε : 0 < ε) (hε' : ε ≤ 1 / 8)
    (hσ₀ : 1 / 2 < σ₀) (hσ₀' : σ₀ ≤ 2)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        D * (2 * q * (3 + |t|) ^ 2) ^ ε) :
    ‖((x + h : ℝ) : ℂ) * Riesz.rieszSum a (x + h) - (x : ℂ) * Riesz.rieszSum a x‖ ≤
      1 / (2 * Real.pi) * (8 * D * (18 * q) ^ ε) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) *
        ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) := by
  have hx0 : 0 < x := by linarith
  have hxh : 0 < x + h := by linarith
  have hM : 0 ≤ (x + h) ^ σ₀ := Real.rpow_nonneg hxh.le _
  have hc : 0 ≤ 8 * D * (18 * q) ^ ε := by positivity
  have hW : 0 ≤ (x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε)) := by
    positivity
  rw [diff_eq_line F hFd a hFL hsum hx hh hD hε.le (by linarith) hσ₀ hσ₀' hB, norm_smul]
  have hpt : ∀ t : ℝ, ‖(((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
        (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)) *
        (F ((σ₀ : ℂ) + (t : ℂ) * I) /
          (((σ₀ : ℂ) + (t : ℂ) * I) * ((σ₀ : ℂ) + (t : ℂ) * I + 1)))‖ ≤
        (8 * D * (18 * q) ^ ε) *
          ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
          (1 + |t|) ^ (-(1 + 2 * ε)) := by
    intro t
    have ht : 0 < 1 + |t| := by positivity
    have hw : ((σ₀ : ℂ) + (t : ℂ) * I + 1).re = σ₀ + 1 := by simp
    have hN1 := cpow_sub_norm_le hx0 hh (by linarith) hw
    have hN2 := cpow_sub_norm_le' hx0 hh (by linarith) hw
    have hz1 : ‖(σ₀ : ℂ) + (t : ℂ) * I + 1‖ ≤ 3 * (1 + |t|) := by
      have he : (σ₀ : ℂ) + (t : ℂ) * I + 1 = ((σ₀ + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast; ring
      rw [he]
      calc ‖((σ₀ + 1 : ℝ) : ℂ) + (t : ℂ) * I‖
          ≤ ‖((σ₀ + 1 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |σ₀ + 1| + |t| := by
            simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 3 * (1 + |t|) := by
            rw [abs_of_pos (by linarith)]; linarith [abs_nonneg t]
    have hA : ‖((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
        (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)‖ ≤ (x + h) ^ σ₀ * (3 * h * (1 + |t|)) := by
      calc _ ≤ ‖(σ₀ : ℂ) + (t : ℂ) * I + 1‖ * (x + h) ^ σ₀ * h := hN1
        _ ≤ 3 * (1 + |t|) * (x + h) ^ σ₀ * h := by gcongr
        _ = (x + h) ^ σ₀ * (3 * h * (1 + |t|)) := by ring
    have hBd : ‖((x + h : ℝ) : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1) -
        (x : ℂ) ^ ((σ₀ : ℂ) + (t : ℂ) * I + 1)‖ ≤ (x + h) ^ σ₀ * (2 * (x + h)) := by
      calc _ ≤ 2 * (x + h) ^ (σ₀ + 1) := hN2
        _ = (x + h) ^ σ₀ * (2 * (x + h)) := by
            rw [Real.rpow_add_one hxh.ne']; ring
    have hint := le_interp (norm_nonneg _) hM (by positivity) (by positivity) hA hBd
      (show 0 ≤ 4 * ε by linarith) (show 4 * ε ≤ 1 by linarith)
    have hQ := quotient_norm_le F (σ := σ₀) (t := t) hσ₀.le hD hε.le (hB σ₀ t le_rfl hσ₀')
    have hsplit : (3 * h * (1 + |t|)) ^ (1 - 4 * ε) =
        (3 * h) ^ (1 - 4 * ε) * (1 + |t|) ^ (1 - 4 * ε) :=
      Real.mul_rpow (by positivity) ht.le
    have hexp : (1 + |t|) ^ (1 - 4 * ε) * (1 + |t|) ^ (-(2 - 2 * ε)) =
        (1 + |t|) ^ (-(1 + 2 * ε)) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [norm_mul]
    calc _ ≤ ((x + h) ^ σ₀ * ((3 * h * (1 + |t|)) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
          (8 * D * (18 * q) ^ ε * (1 + |t|) ^ (-(2 - 2 * ε))) :=
          mul_le_mul hint hQ (norm_nonneg _) (by positivity)
      _ = (8 * D * (18 * q) ^ ε) *
            ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
            ((1 + |t|) ^ (1 - 4 * ε) * (1 + |t|) ^ (-(2 - 2 * ε))) := by
          rw [hsplit]; ring
      _ = _ := by rw [hexp]
  have hI := integrable_decay (r := 1 + 2 * ε) (by linarith)
  have hpi : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hpi]
  have hbound := norm_integral_le_of_norm_le
    (hI.const_mul ((8 * D * (18 * q) ^ ε) *
      ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε)))))
    (Eventually.of_forall hpt)
  rw [integral_const_mul] at hbound
  calc _ ≤ 1 / (2 * Real.pi) * ((8 * D * (18 * q) ^ ε) *
        ((x + h) ^ σ₀ * ((3 * h) ^ (1 - 4 * ε) * (2 * (x + h)) ^ (4 * ε))) *
        ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) := by gcongr
    _ = _ := by ring

/-- **Generic partial-sum bound.** If `F = L(a, ·)` on `re s > 1`, `F` is holomorphic on
`re s > 1/2`, `‖a n‖ ≤ 1`, and `‖F(σ + it)‖ ≤ D (2 q (3 + |t|)^2)^ε` on `σ₀ ≤ σ ≤ 2`, then
`‖∑_{n ≤ x} a(n)‖ ≤ K q^ε x^{σ₀ + 4ε}` for `x ≥ 1`. -/
theorem sum_bound {q : ℕ} (F : ℂ → ℂ) (hFd : ∀ z : ℂ, 1 / 2 < z.re → DifferentiableAt ℂ F z)
    (a : ℕ → ℂ) (hFL : ∀ z : ℂ, 1 < z.re → F z = LSeries a z)
    (hsum : LSeriesSummable a ((2 : ℝ) : ℂ)) (ha : ∀ n, ‖a n‖ ≤ 1)
    {D ε σ₀ : ℝ} (hD : 0 ≤ D) (hε : 0 < ε) (hε' : ε ≤ 1 / 8) (hσ₀ : 1 / 2 < σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hq : (1 : ℝ) ≤ q)
    (hB : ∀ σ t : ℝ, σ₀ ≤ σ → σ ≤ 2 →
      ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (2 * q * (3 + |t|) ^ 2) ^ ε)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤
      (1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24 + 2) *
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
  have hun := CharSum.unsmooth a ha hx0 hh0
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
        h * (h + 1) := hun
  set c := 1 / (2 * Real.pi) * (8 * D * 18) * J * 24 with hc
  have hmain : h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤ h * (c * Q * X + h + 1) := by
    calc h * ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖
        ≤ 1 / (2 * Real.pi) * (8 * D * (18 * Q)) * J * (24 * h * X) + h * (h + 1) := by
          linarith [hun', hdiff, hstep]
      _ = h * (c * Q * X + h + 1) := by rw [hc]; ring
  have hS := le_of_mul_le_mul_left hmain hh0
  have hQX : X ≤ Q * X := by nlinarith
  show ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n‖ ≤ (c + 2) * Q * X
  nlinarith

end LiouvilleEnergyRH.Contour
