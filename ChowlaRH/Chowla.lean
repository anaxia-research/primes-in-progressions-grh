/-
Chowla's conjecture: correlations, sign patterns, and the one-point case under RH.
-/
import ChowlaRH.MertensTransfer

open ArithmeticFunction Finset Filter Topology Real

namespace ChowlaRH

/-- The Liouville function as a real-valued sequence. -/
noncomputable abbrev lam (n : ℕ) : ℝ := (liouville n : ℝ)

theorem lam_eq_or {n : ℕ} (hn : n ≠ 0) : lam n = 1 ∨ lam n = -1 := by
  unfold lam
  rw [liouville_apply hn]
  rcases neg_one_pow_eq_or ℤ (cardFactors n) with h | h <;> simp [h]

/-- The correlation `∏_{h ∈ H} λ(n + h)` attached to a finite set of shifts. -/
noncomputable def corr (H : Finset ℕ) (n : ℕ) : ℝ := ∏ h ∈ H, lam (n + h)

/-- The weighted average of `f` over `1 ≤ n ≤ N` with weights `w`. -/
noncomputable def wavg (w : ℕ → ℝ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Ioc 0 N, w n * f n) / ∑ n ∈ Ioc 0 N, w n

/-- Natural (Cesàro) weights. -/
noncomputable def natW : ℕ → ℝ := fun _ => 1

/-- Logarithmic weights `1/n`. -/
noncomputable def logW : ℕ → ℝ := fun n => 1 / (n : ℝ)

/-- The correlation with shift set `H` has mean zero for the weights `w`. -/
def ChowlaAt (w : ℕ → ℝ) (H : Finset ℕ) : Prop :=
  Tendsto (wavg w (corr H)) atTop (𝓝 0)

/-- Chowla's conjecture of order `k` for the weights `w`. -/
def ChowlaOrder (w : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → ChowlaAt w H

/-- Chowla's conjecture (all orders) for the weights `w`.  With `w = natW` this is
the conjecture as stated by Chowla; with `w = logW` it is the logarithmic form. -/
def Chowla (w : ℕ → ℝ) : Prop := ∀ k : ℕ, 1 ≤ k → ChowlaOrder w k

/-! ### The one-point case from a power bound for `L(N)` -/

theorem sum_shift_eq (h N : ℕ) :
    ∑ n ∈ Ioc 0 N, lam (n + h) =
      (summatoryLiouville (N + h) : ℝ) - (summatoryLiouville h : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N), ih, show N + 1 + h = (N + h) + 1 by ring]
    unfold summatoryLiouville
    rw [sum_Ioc_succ_top (Nat.zero_le _)]
    push_cast
    ring

/-- If `L(N) ≪ N^θ` with `θ < 1`, then every one-point correlation has natural mean zero. -/
theorem chowlaAt_single_of_liouvilleBound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hL : LiouvilleBound θ) (h : ℕ) : ChowlaAt natW {h} := by
  obtain ⟨C, hC⟩ := hL
  have hC0 : 0 ≤ C := by
    have := hC 1
    have h1 : summatoryLiouville 1 = 1 := by simp [summatoryLiouville, liouville_apply_one]
    simp [h1] at this
    linarith
  unfold ChowlaAt
  refine squeeze_zero_norm' (a := fun N : ℕ => 3 * C * (N : ℝ) ^ (θ - 1)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (max h 1)] with N hN
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNh : h ≤ N := le_of_max_le_left hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hW : ∑ n ∈ Ioc 0 N, natW n = N := by simp [natW]
    have hnum : ∑ n ∈ Ioc 0 N, natW n * corr {h} n = ∑ n ∈ Ioc 0 N, lam (n + h) := by
      simp [natW, corr]
    rw [Real.norm_eq_abs, wavg, hW, hnum, sum_shift_eq, abs_div, abs_of_pos hNpos]
    rw [rpow_sub_one hNpos.ne', ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hNpos.le
    have h2 : ((N + h : ℕ) : ℝ) ^ θ ≤ 2 * (N : ℝ) ^ θ := by
      have : ((N + h : ℕ) : ℝ) ≤ 2 * N := by push_cast; exact_mod_cast (by omega : N + h ≤ 2 * N)
      calc ((N + h : ℕ) : ℝ) ^ θ ≤ (2 * (N : ℝ)) ^ θ :=
            rpow_le_rpow (Nat.cast_nonneg _) this hθ0
        _ = (2 : ℝ) ^ θ * (N : ℝ) ^ θ := mul_rpow (by norm_num) hNpos.le
        _ ≤ 2 * (N : ℝ) ^ θ := by
            refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg hNpos.le _)
            simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1.le
    have h3 : (h : ℝ) ^ θ ≤ (N : ℝ) ^ θ :=
      rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNh) hθ0
    calc |(summatoryLiouville (N + h) : ℝ) - (summatoryLiouville h : ℝ)|
        ≤ |(summatoryLiouville (N + h) : ℝ)| + |(summatoryLiouville h : ℝ)| := abs_sub _ _
      _ ≤ C * ((N + h : ℕ) : ℝ) ^ θ + C * (h : ℝ) ^ θ := add_le_add (hC _) (hC _)
      _ ≤ C * (2 * (N : ℝ) ^ θ) + C * (N : ℝ) ^ θ :=
          add_le_add (mul_le_mul_of_nonneg_left h2 hC0) (mul_le_mul_of_nonneg_left h3 hC0)
      _ = 3 * C * (N : ℝ) ^ θ := by ring
  · have : Tendsto (fun N : ℕ => (N : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - θ) (by linarith)).comp
        tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, neg_sub] using this
    simpa using this.const_mul (3 * C)

/-- Under Littlewood's form of RH, Chowla's conjecture of order one holds
(with natural averaging), for every shift. -/
theorem chowlaOrder_one_of_littlewoodRH (hRH : LittlewoodRH) : ChowlaOrder natW 1 := by
  intro H hH
  obtain ⟨h, rfl⟩ := card_eq_one.mp hH
  exact chowlaAt_single_of_liouvilleBound (θ := 1 / 2 + 1 / 4) (by norm_num) (by norm_num)
    (liouvilleBound_of_littlewoodRH hRH (1 / 4) (by norm_num)) h

end ChowlaRH
