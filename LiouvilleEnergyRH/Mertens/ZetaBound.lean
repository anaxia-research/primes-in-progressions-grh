import Mathlib

/-!
# A bound for `ζ(s)` on `re s ≥ 1/2`

For `re s > 0` the Abel integral `G(s) = s ∫_1^∞ (⌊t⌋ - t) t^{-s-1} dt` is holomorphic and
`‖G(s)‖ ≤ ‖s‖ / re s`. For `re s > 1` it equals `ζ(s) - s/(s-1)`, so by analytic continuation
`ζ(s) = 1/(s-1) + 1 + G(s)` for `re s > 0`, `s ≠ 1`. Hence
`‖ζ(s)‖ ≤ 1/‖s - 1‖ + 1 + 2‖s‖` for `re s ≥ 1/2`, `s ≠ 1`.
-/

namespace LiouvilleEnergyRH.ZetaBound

open Finset Filter Asymptotics MeasureTheory Complex
open scoped Topology

/-- The sawtooth `⌊t⌋ - t`. -/
noncomputable def saw (t : ℝ) : ℂ := ((⌊t⌋₊ : ℕ) : ℂ) - (t : ℂ)

lemma saw_measurable : Measurable saw := by
  unfold saw
  exact ((measurable_from_nat (f := fun n : ℕ => (n : ℂ))).comp Nat.measurable_floor).sub
    Complex.measurable_ofReal

lemma saw_norm {t : ℝ} (ht : 0 ≤ t) : ‖saw t‖ ≤ 1 := by
  unfold saw
  have h1 := Nat.floor_le ht
  have h2 := Nat.lt_floor_add_one t
  have he : ((⌊t⌋₊ : ℕ) : ℂ) - (t : ℂ) = (((⌊t⌋₊ : ℝ) - t : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

noncomputable def kernel (s : ℂ) (t : ℝ) : ℂ := saw t * (t : ℂ) ^ (-(s + 1))

/-- The Abel integral `G(s) = s ∫_1^∞ (⌊t⌋ - t) t^{-s-1} dt`. -/
noncomputable def abel (s : ℂ) : ℂ := s * ∫ t in Set.Ioi (1 : ℝ), kernel s t

lemma kernel_measurable (s : ℂ) :
    AEStronglyMeasurable (kernel s) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  exact saw_measurable.aestronglyMeasurable.mul (hpow.aestronglyMeasurable measurableSet_Ioi)

lemma kernel_norm_le (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖kernel s t‖ ≤ t ^ (-(s.re + 1)) := by
  rw [kernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht),
    Complex.neg_re, Complex.add_re, Complex.one_re]
  calc ‖saw t‖ * t ^ (-(s.re + 1)) ≤ 1 * t ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right (saw_norm (by linarith))
          (Real.rpow_nonneg (zero_lt_one.trans ht).le _)
    _ = _ := one_mul _

lemma kernel_integral_norm {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), kernel s t‖ ≤ 1 / s.re := by
  have hexp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt hexp zero_lt_one)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact kernel_norm_le s ht
    _ = 1 / s.re := by
      rw [integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
      field_simp [ne_of_gt hs]
      ring

theorem abel_norm {s : ℂ} (hs : 0 < s.re) : ‖abel s‖ ≤ ‖s‖ / s.re := by
  rw [abel, norm_mul]
  calc _ ≤ ‖s‖ * (1 / s.re) :=
        mul_le_mul_of_nonneg_left (kernel_integral_norm hs) (norm_nonneg s)
    _ = _ := by ring

/-- The input to the Mellin transform. -/
noncomputable def input : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator saw

lemma input_measurable : Measurable input := saw_measurable.indicator measurableSet_Ioi

lemma input_norm (t : ℝ) : ‖input t‖ ≤ 1 := by
  by_cases ht : 1 < t
  · simpa only [input, Set.mem_Ioi, Set.indicator_apply, ite_eq_left ht] using
      saw_norm (show 0 ≤ t by linarith)
  · simp only [input, Set.mem_Ioi, Set.indicator_apply, ite_eq_right ht, norm_zero]
    exact zero_le_one

lemma input_locallyIntegrable : LocallyIntegrableOn input (Set.Ioi (0 : ℝ)) := by
  refine (locallyIntegrableOn_const (s := Set.Ioi (0 : ℝ)) (1 : ℝ)).mono
    input_measurable.aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by simpa using input_norm t

lemma input_bigO_atTop : input =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using input_norm t

lemma input_bigO_zero (b : ℝ) : input =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hnot : t ∉ Set.Ioi (1 : ℝ) := by change ¬1 < t; linarith
  simp only [input, Set.indicator_of_notMem hnot, norm_zero, zero_mul, le_refl]

lemma abel_eq_mellin (s : ℂ) : abel s = s * mellin input (-s) := by
  unfold abel mellin
  congr 1
  have heq : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • input t) =
      (Set.Ioi (1 : ℝ)).indicator (kernel s) := by
    funext t
    by_cases ht : 1 < t
    · simp only [input, Set.indicator_apply, Set.mem_Ioi, ite_eq_left ht, smul_eq_mul, kernel]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · have hn : t ∉ Set.Ioi (1 : ℝ) := ht
      simp only [input, Set.indicator_of_notMem hn, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Ioi]
  rw [Set.inter_eq_right.mpr (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) from
    fun t ht => lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)]

theorem abel_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ abel s := by
  have hm : DifferentiableAt ℂ (mellin input) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow input_locallyIntegrable input_bigO_atTop
      (b := -s.re - 1)
    · simpa only [Complex.neg_re] using neg_neg_of_pos hs
    · exact input_bigO_zero _
    · simp only [Complex.neg_re]
      linarith
  have heq : abel = fun z => z * mellin input (-z) := funext abel_eq_mellin
  rw [heq]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- `ζ(s) = s ∫_1^∞ ⌊t⌋ t^{-s-1} dt` for `re s > 1`. -/
lemma zeta_eq_floor_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, (1 : ℕ → ℂ) k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun n => ?_⟩
    simp
  have h := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hs
    (LSeriesSummable_one_iff.mpr hs) hO
  rw [h]
  congr 2
  funext t
  simp

lemma floor_kernel_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
  have hmaj : IntegrableOn (fun t : ℝ => t ^ (-s.re)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  refine hmaj.mono' ?_ ?_
  · exact ((measurable_from_nat (f := fun n : ℕ => (n : ℂ))).comp
      Nat.measurable_floor).aestronglyMeasurable.mul (hpow.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_natCast]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    calc (⌊t⌋₊ : ℝ) * t ^ (-(s.re + 1)) ≤ t * t ^ (-(s.re + 1)) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le ht0.le) (Real.rpow_nonneg ht0.le _)
      _ = t ^ (-s.re) := by
          rw [show -s.re = 1 + (-(s.re + 1)) by ring, Real.rpow_add ht0, Real.rpow_one]

lemma id_kernel_integral {s : ℂ} (hs : 1 < s.re) :
    s * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = s / (s - 1) := by
  have heq : ∀ t ∈ Set.Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    rw [show -s = 1 + (-(s + 1)) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : (s - 1).re = 0 := by rw [h]; simp
    simp at this
    linarith
  have h1 : -s + 1 ≠ 0 := by
    intro h; apply hs1; linear_combination -h
  simp only [Complex.ofReal_one, Complex.one_cpow]
  field_simp
  ring

lemma id_kernel_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
  have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  refine hI.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
  dsimp only
  rw [show -s = 1 + (-(s + 1)) by ring, Complex.cpow_add _ _ ht0, Complex.cpow_one]

lemma abel_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) : abel s = riemannZeta₀ s - 1 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hk : (fun t : ℝ => kernel s t) = fun t : ℝ =>
      ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) - (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    funext t; simp only [kernel, saw]; ring
  rw [abel, hk, integral_sub (floor_kernel_integrable hs) (id_kernel_integrable hs), mul_sub,
    ← zeta_eq_floor_integral hs, id_kernel_integral hs, riemannZeta_eq_inv_sub_add hs1]
  field_simp
  ring

/-- `G(s) = ζ₀(s) - 1` throughout `re s > 0`. -/
theorem abel_eq {s : ℂ} (hs : 0 < s.re) : abel s = riemannZeta₀ s - 1 := by
  let U : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hF : AnalyticOnNhd ℂ (fun z => riemannZeta₀ z - 1) U :=
    ((differentiable_riemannZeta₀.sub_const 1).differentiableOn).analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ abel U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    exact (abel_differentiableAt hz).differentiableWithinAt
  have heq : abel =ᶠ[𝓝 (2 : ℂ)] (fun z => riemannZeta₀ z - 1) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    exact abel_eq_of_one_lt hz
  exact hG.eqOn_of_preconnected_of_eventuallyEq hF hc.isPreconnected
    (show (2 : ℂ) ∈ U by change 0 < (2 : ℂ).re; norm_num) heq hs

/-- **Growth of `ζ`.** `‖ζ(s)‖ ≤ 1/‖s - 1‖ + 1 + 2‖s‖` for `re s ≥ 1/2`, `s ≠ 1`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + 2 * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  have hz : riemannZeta s = (s - 1)⁻¹ + 1 + abel s := by
    rw [abel_eq hs0, riemannZeta_eq_inv_sub_add hs1]; ring
  have hA : ‖abel s‖ ≤ 2 * ‖s‖ := by
    calc ‖abel s‖ ≤ ‖s‖ / s.re := abel_norm hs0
      _ ≤ ‖s‖ / (1 / 2) := div_le_div_of_nonneg_left (norm_nonneg s) (by norm_num) hs
      _ = 2 * ‖s‖ := by ring
  rw [hz]
  calc ‖(s - 1)⁻¹ + 1 + abel s‖ ≤ ‖(s - 1)⁻¹‖ + ‖(1 : ℂ)‖ + ‖abel s‖ := norm_add₃_le
    _ ≤ 1 / ‖s - 1‖ + 1 + 2 * ‖s‖ := by
        rw [norm_inv, norm_one, one_div]; linarith

end LiouvilleEnergyRH.ZetaBound
