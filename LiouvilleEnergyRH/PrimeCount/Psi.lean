import LiouvilleEnergyRH.PrimeCount.ContourB
import LiouvilleEnergyRH.Mertens.Main
import Mathlib.NumberTheory.Chebyshev

/-!
# Von Koch's bound for `ψ(x)` under the zero-free half-plane

If `ζ(s) ≠ 0` for `re s > 1/2`, then `ψ(x) = x + O_η(x^{1/2 + η})` for every `η > 0`.

With `Z = ζ₁ = (s - 1) ζ(s)` (entire, `Z(1) = 1`), the function
`F(s) = - Z'(s)/Z(s) - dslope Z 1 s` is holomorphic on `re s > 1/2` and equals
`-ζ'/ζ(s) - ζ(s) = ∑ (Λ(n) - 1) n^{-s}` on `re s > 1`: the poles of `-ζ'/ζ` and `ζ` at `s = 1`
cancel. The logarithmic control lemma bounds `ζ` and `ζ'/ζ` on `σ ≥ 1/2 + 8e`, `|t| > 2`.
-/

namespace LiouvilleEnergyRH.PrimeCount

open Complex Set Metric Filter ArithmeticFunction Vinogradov
open scoped LSeries.notation

/-- `-ζ'/ζ(s) - ζ(s)`, continued across `s = 1`. -/
noncomputable def G (s : ℂ) : ℂ :=
  -(deriv riemannZeta₁ s) / riemannZeta₁ s - dslope riemannZeta₁ 1 s

lemma deriv_zeta₁ {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev : riemannZeta₁ =ᶠ[nhds s] fun z => (z - 1) * riemannZeta z := by
    have : ∀ᶠ z in nhds s, z ≠ 1 := isOpen_ne.mem_nhds hs
    filter_upwards [this] with z hz using Mertens.zeta₁_eq hz
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [hd.deriv]; ring

lemma G_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    G s = -(deriv riemannZeta s) / riemannZeta s - riemannZeta s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [G, deriv_zeta₁ hs, Mertens.zeta₁_eq hs, dslope_of_ne _ hs, slope_def_field,
    Mertens.zeta₁_eq hs, riemannZeta₁_one]
  field_simp
  ring

section
variable (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
include hz

lemma G_differentiableAt {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ G s := by
  have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta₁) s :=
    ((hZ.analyticAt s).deriv).differentiableAt
  have hd2 : DifferentiableAt ℂ (dslope riemannZeta₁ 1) s :=
    ((Complex.differentiableOn_dslope (s := univ) Filter.univ_mem).mpr
      hZ.differentiableOn).differentiableAt Filter.univ_mem
  exact (hd1.neg.div hZ.differentiableAt (Mertens.zeta₁_ne_zero hz hs)).sub hd2

end

/-- The coefficients `Λ(n) - 1`. -/
noncomputable def coef : ℕ → ℂ := fun n => (↗vonMangoldt : ℕ → ℂ) n - 1

lemma G_eq_LSeries {s : ℂ} (hs : 1 < s.re) : G s = LSeries coef s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hc : coef = (↗vonMangoldt : ℕ → ℂ) - 1 := by funext n; simp [coef]
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  rw [G_eq hs1 hz, hc, LSeries_sub (LSeriesSummable_vonMangoldt hs) h1,
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries_one_eq_riemannZeta hs]

lemma coef_summable : LSeriesSummable coef ((2 : ℝ) : ℂ) := by
  have hs : 1 < (((2 : ℝ) : ℂ)).re := by simp
  exact (LSeriesSummable_vonMangoldt hs).sub (LSeriesSummable_one_iff.mpr hs)

lemma coef_norm_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) (hn : (n : ℝ) ≤ 2 * x) :
    ‖coef n‖ ≤ Real.log (2 * x) + 1 := by
  have hL0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
  have hL : vonMangoldt n ≤ Real.log (2 * x) := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp; exact Real.log_nonneg (by linarith)
    · exact vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hpos) hn)
  have : coef n = (((vonMangoldt n - 1 : ℝ)) : ℂ) := by simp [coef]
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hlog : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  constructor <;> linarith

/-- **Bound for `G = -ζ'/ζ - ζ` on vertical strips.** -/
theorem G_bound (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ t : ℝ, 1 / 2 + 8 * e ≤ σ → σ ≤ 2 →
      ‖G ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := by
  obtain ⟨D₁, hD₁, hctrl⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := EulerLog.eulerLogBound) (M := 1) (ε := ε) he he'
    EulerLog.eulerLogBound_ge_one le_rfl hε
  set K₀ : ℝ := OAI.SevenEighths.LogarithmicControl.outerConstant e EulerLog.eulerLogBound 1 /
    (2 * e) with hK₀
  have hK₀0 : 0 ≤ K₀ := by
    have hA := EulerLog.eulerLogBound_ge_one
    rw [hK₀, OAI.SevenEighths.LogarithmicControl.outerConstant]
    positivity
  set K : Set ℂ := Icc (1 / 2 + 8 * e) 2 ×ℂ Icc (-2) 2 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn G K := by
    intro z hzK
    have hre : 1 / 2 < z.re := by
      have := (Complex.mem_reProdIm.mp hzK).1.1; linarith
    exact (G_differentiableAt hz hre).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨D₁ + K₀ / ε + |B|, by positivity, ?_⟩
  intro σ t hσ hσ'
  set C : ℝ := 2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2 with hCdef
  have hbase : 1 ≤ C := by
    rw [hCdef]; push_cast; nlinarith [abs_nonneg t]
  have hpow : 1 ≤ C ^ ε := Real.one_le_rpow hbase hε.le
  by_cases ht : |t| ≤ 2
  · have hmem : ((σ : ℂ) + (t : ℂ) * I) ∈ K := by
      rw [hK, Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨hσ, hσ'⟩, abs_le.mp ht⟩
    have h1 := hB _ hmem
    have h2 : B ≤ |B| := le_abs_self B
    have h3 : 0 ≤ (D₁ + K₀ / ε) * C ^ ε := by positivity
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
        have h := Mertens.zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        exact (differentiableAt_riemannZeta h.1).differentiableWithinAt)
      (fun z hzb => by
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hzb
        have h := Mertens.zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        exact hz z (by linarith) h.1)
      (fun z hzb => by
        have hz2 : z ∈ ball (2 + (t : ℂ) * I) (2 - 1 / 2 - 2 * e) :=
          ball_subset_ball (by linarith) hzb
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hz2
        have h := Mertens.zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        rw [Real.rpow_one]
        exact_mod_cast h.2)
      hEd hEe hEb
    have hmem := OAI.SevenEighths.LogarithmicControl.same_height_mem_disk (a := 1 / 2) (e := e)
      (t := t) (v := 8 * e) le_rfl hσ hσ'
    have hb1 := hres.1 _ (closedBall_subset_closedBall (by linarith) hmem)
    have hb2 := hres.2 _ hmem
    have hne : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at ht; simp at ht; linarith
    have hre : 1 / 2 < ((σ : ℂ) + (t : ℂ) * I).re := by simp; linarith
    rw [G_eq hne (hz _ hre hne)]
    set w := (σ : ℂ) + (t : ℂ) * I
    have hlog : Real.log C ≤ C ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
    have hz1 : ‖riemannZeta w‖ ≤ D₁ * C ^ ε := by
      exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) hb1
    have hz2 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ K₀ / ε * C ^ ε := by
      calc ‖deriv riemannZeta w / riemannZeta w‖ ≤ K₀ * Real.log C := by rw [hCdef]; exact hb2
        _ ≤ K₀ * (C ^ ε / ε) := mul_le_mul_of_nonneg_left hlog hK₀0
        _ = K₀ / ε * C ^ ε := by ring
    have hBC : 0 ≤ |B| * C ^ ε := by positivity
    calc ‖-deriv riemannZeta w / riemannZeta w - riemannZeta w‖
        ≤ ‖deriv riemannZeta w / riemannZeta w‖ + ‖riemannZeta w‖ := by
          rw [neg_div]; exact (norm_sub_le _ _).trans (by rw [norm_neg])
      _ ≤ K₀ / ε * C ^ ε + D₁ * C ^ ε := add_le_add hz2 hz1
      _ ≤ (D₁ + K₀ / ε + |B|) * C ^ ε := by nlinarith

/-- **Von Koch's bound for `ψ`.** If `ζ(s) ≠ 0` for `re s > 1/2`, then for every `η > 0` there
is `K` with `|ψ(x) - x| ≤ K x^{1/2 + η}` for all `x ≥ 1`. -/
theorem psi_bound (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ x : ℝ, 1 ≤ x → |Chebyshev.psi x - x| ≤ K * x ^ (1 / 2 + η) := by
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
  obtain ⟨D, hD, hDb⟩ := G_bound hz he he' hε
  set c : ℝ := 1 / (2 * Real.pi) * (8 * D * 18) * (∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε))) * 24
    with hc
  have hJ0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ (-(1 + 2 * ε)) :=
    MeasureTheory.integral_nonneg (fun t => by positivity)
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c + 4 + 8 / dd + 1, ?_⟩
  intro x hx
  have hx0 : 0 < x := by linarith
  set Bx : ℝ := Real.log (2 * x) + 1 with hBx
  have hlog0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hBx0 : 0 ≤ Bx := by linarith
  have h := Contour.sum_bound_B (q := 1) G (fun z hz' => G_differentiableAt hz hz')
    coef (fun z hz' => G_eq_LSeries hz') coef_summable hBx0 hD hε hε8
    (show 1 / 2 < 1 / 2 + 8 * e by linarith) (by linarith) (by simp) hDb x hx
    (fun n hn => coef_norm_le hx n hn)
  rw [show ((1 : ℕ) : ℝ) ^ ε = 1 by simp, mul_one] at h
  -- the sum of the coefficients
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, coef n =
      ((Chebyshev.psi x - (⌊x⌋₊ : ℝ) : ℝ) : ℂ) := by
    simp only [coef, Finset.sum_sub_distrib, Chebyshev.psi]
    push_cast
    simp
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at h
  have hX : x ^ (1 / 2 + 8 * e + 4 * ε) ≤ x ^ (1 / 2 + η' - dd) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [hε_def, hdd]; linarith)
  have hlogx : Real.log (2 * x) ≤ 2 / dd * x ^ dd := by
    have := Real.log_le_rpow_div (show 0 ≤ 2 * x by linarith) hdd0
    have h2 : (2 * x) ^ dd ≤ 2 * x ^ dd := by
      rw [Real.mul_rpow (by norm_num) hx0.le]
      have : (2 : ℝ) ^ dd ≤ 2 := by
        calc (2 : ℝ) ^ dd ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hdd]; linarith)
          _ = 2 := Real.rpow_one 2
      nlinarith [Real.rpow_nonneg hx0.le dd]
    calc Real.log (2 * x) ≤ (2 * x) ^ dd / dd := this
      _ ≤ 2 * x ^ dd / dd := by gcongr
      _ = 2 / dd * x ^ dd := by ring
  have hxdd : 1 ≤ x ^ dd := Real.one_le_rpow hx hdd0.le
  have hsplit : x ^ (1 / 2 + η' - dd) * x ^ dd = x ^ (1 / 2 + η') := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hY0 : 0 ≤ x ^ (1 / 2 + η' - dd) := by positivity
  have hmain : |Chebyshev.psi x - (⌊x⌋₊ : ℝ)| ≤ (c + 4 + 8 / dd) * x ^ (1 / 2 + η') := by
    have h1 : (c + 2 * Bx) * x ^ (1 / 2 + 8 * e + 4 * ε) ≤
        (c + 2 * Bx) * x ^ (1 / 2 + η' - dd) := by gcongr
    have h2 : (c + 2 * Bx) ≤ (c + 4 + 8 / dd) * x ^ dd := by
      rw [hBx]
      have h8 : 0 ≤ 8 / dd := by positivity
      have ha : c ≤ c * x ^ dd := le_mul_of_one_le_right hc0 hxdd
      have hb : (4 : ℝ) ≤ 4 * x ^ dd := by linarith
      have hc' : 2 * Real.log (2 * x) ≤ 8 / dd * x ^ dd := by
        have : 2 * (2 / dd * x ^ dd) ≤ 8 / dd * x ^ dd := by
          have hx0' : 0 ≤ x ^ dd := by positivity
          have : 2 * (2 / dd) ≤ 8 / dd := by
            rw [mul_div_assoc', div_le_div_iff_of_pos_right hdd0]; norm_num
          nlinarith
        linarith
      nlinarith
    calc |Chebyshev.psi x - (⌊x⌋₊ : ℝ)| ≤ (c + 2 * Bx) * x ^ (1 / 2 + 8 * e + 4 * ε) := h
      _ ≤ (c + 2 * Bx) * x ^ (1 / 2 + η' - dd) := h1
      _ ≤ (c + 4 + 8 / dd) * x ^ dd * x ^ (1 / 2 + η' - dd) := by gcongr
      _ = (c + 4 + 8 / dd) * x ^ (1 / 2 + η') := by rw [mul_assoc, mul_comm (x ^ dd), hsplit]
  have hfl : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Nat.lt_floor_add_one x]
    · linarith [Nat.floor_le hx0.le]
  have hxη : x ^ (1 / 2 + η') ≤ x ^ (1 / 2 + η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hx1 : 1 ≤ x ^ (1 / 2 + η) := Real.one_le_rpow hx (by linarith)
  have hK0 : 0 ≤ c + 4 + 8 / dd := by positivity
  calc |Chebyshev.psi x - x| = |(Chebyshev.psi x - (⌊x⌋₊ : ℝ)) + ((⌊x⌋₊ : ℝ) - x)| := by ring_nf
    _ ≤ |Chebyshev.psi x - (⌊x⌋₊ : ℝ)| + |(⌊x⌋₊ : ℝ) - x| := abs_add_le _ _
    _ ≤ (c + 4 + 8 / dd) * x ^ (1 / 2 + η') + 1 := add_le_add hmain hfl
    _ ≤ (c + 4 + 8 / dd) * x ^ (1 / 2 + η) + x ^ (1 / 2 + η) := by gcongr
    _ = (c + 4 + 8 / dd + 1) * x ^ (1 / 2 + η) := by ring

end LiouvilleEnergyRH.PrimeCount
