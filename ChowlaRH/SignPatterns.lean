/-
Sign patterns of the Liouville function from Chowla-type correlation estimates.

If every correlation `∏_{h ∈ S} λ(n + h)` with `∅ ≠ S ⊆ H` has `w`-mean zero, then every
sign pattern `ε : H → {±1}` is taken by `(λ(n + h))_{h ∈ H}` with `w`-density `2^{-|H|}`.
-/
import ChowlaRH.Chowla

open ArithmeticFunction Finset Filter Topology Real

namespace ChowlaRH

/-- The indicator that `λ(n + h) = ε h` for every `h ∈ H`. -/
noncomputable def patternInd (H : Finset ℕ) (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  if ∀ h ∈ H, lam (n + h) = ε h then 1 else 0

/-- A sign vector: `ε h = ±1` on `H`. -/
def IsSignVec (H : Finset ℕ) (ε : ℕ → ℝ) : Prop := ∀ h ∈ H, ε h = 1 ∨ ε h = -1

theorem factor_eq {x e : ℝ} (hx : x = 1 ∨ x = -1) (he : e = 1 ∨ e = -1) :
    (1 + e * x) / 2 = if x = e then 1 else 0 := by
  rcases hx with rfl | rfl <;> rcases he with rfl | rfl <;> norm_num

/-- The pattern indicator as a product of `(1 + ε_h λ(n+h))/2`. -/
theorem patternInd_eq_prod (H : Finset ℕ) {ε : ℕ → ℝ} (hε : IsSignVec H ε) {n : ℕ}
    (hn : 0 < n) :
    patternInd H ε n = ∏ h ∈ H, (1 + ε h * lam (n + h)) / 2 := by
  have hf : ∀ h ∈ H, (1 + ε h * lam (n + h)) / 2 = if lam (n + h) = ε h then 1 else 0 :=
    fun h hh => factor_eq (lam_eq_or (by omega)) (hε h hh)
  rw [prod_congr rfl hf, patternInd]
  split_ifs with hall
  · exact (prod_eq_one fun h hh => by simp [hall h hh]).symm
  · push Not at hall
    obtain ⟨h, hh, hne⟩ := hall
    exact (prod_eq_zero hh (by simp [hne])).symm

/-- Expansion of the pattern indicator into correlations. -/
theorem patternInd_expand (H : Finset ℕ) {ε : ℕ → ℝ} (hε : IsSignVec H ε) {n : ℕ}
    (hn : 0 < n) :
    patternInd H ε n =
      (1 / 2) ^ H.card * ∑ S ∈ H.powerset, (∏ h ∈ S, ε h) * corr S n := by
  rw [patternInd_eq_prod H hε hn, prod_div_distrib, prod_const, prod_one_add]
  rw [div_eq_mul_inv, mul_comm, one_div, inv_pow]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [corr, ← prod_mul_distrib]

/-- Linearity of the weighted average over a finite family. -/
theorem wavg_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ℕ → ℝ) (g : ι → ℕ → ℝ) (N : ℕ) :
    wavg w (fun n => ∑ i ∈ s, c i * g i n) N = ∑ i ∈ s, c i * wavg w (g i) N := by
  unfold wavg
  simp only [mul_div_assoc']
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun i _ => by ring

/-- **Sign-pattern theorem.**  Positive weights; vanishing `w`-means of all correlations
with nonempty `S ⊆ H`; then the pattern `ε` has `w`-density `2^{-|H|}`. -/
theorem tendsto_pattern (w : ℕ → ℝ) (hw : ∀ n, 0 < n → 0 < w n) (H : Finset ℕ)
    {ε : ℕ → ℝ} (hε : IsSignVec H ε) (hC : ∀ S ⊆ H, S.Nonempty → ChowlaAt w S) :
    Tendsto (wavg w (patternInd H ε)) atTop (𝓝 ((1 / 2) ^ H.card)) := by
  -- rewrite the pattern average as a combination of correlation averages
  have hrw : ∀ N, wavg w (patternInd H ε) N =
      (1 / 2) ^ H.card * ∑ S ∈ H.powerset, (∏ h ∈ S, ε h) * wavg w (corr S) N := by
    intro N
    have : wavg w (patternInd H ε) N =
        wavg w (fun n => ∑ S ∈ H.powerset, ((1 / 2) ^ H.card * ∏ h ∈ S, ε h) * corr S n) N := by
      unfold wavg
      congr 1
      refine sum_congr rfl fun n hn => ?_
      rw [patternInd_expand H hε (mem_Ioc.mp hn).1, mul_sum]
      congr 1
      refine sum_congr rfl fun S _ => ?_
      ring
    rw [this, wavg_sum, mul_sum]
    refine sum_congr rfl fun S _ => ?_
    ring
  rw [show wavg w (patternInd H ε) = fun N =>
      (1 / 2) ^ H.card * ∑ S ∈ H.powerset, (∏ h ∈ S, ε h) * wavg w (corr S) N from funext hrw]
  -- limit of each term
  have hlim : ∀ S ∈ H.powerset, Tendsto (fun N => (∏ h ∈ S, ε h) * wavg w (corr S) N) atTop
      (𝓝 (if S = ∅ then 1 else 0)) := by
    intro S hS
    by_cases h0 : S = ∅
    · subst h0
      simp only [prod_empty, one_mul, ite_true]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hpos : 0 < ∑ n ∈ Ioc 0 N, w n :=
        sum_pos (fun n hn => hw n (mem_Ioc.mp hn).1) ⟨1, mem_Ioc.mpr ⟨by norm_num, hN⟩⟩
      simp [wavg, corr, hpos.ne']
    · rw [show (if S = ∅ then (1 : ℝ) else 0) = 0 by simp [h0]]
      have := (hC S (mem_powerset.mp hS) (nonempty_iff_ne_empty.mpr h0)).const_mul
        (∏ h ∈ S, ε h)
      simpa using this
  have hsum := tendsto_finsetSum _ hlim
  have hval : ∑ S ∈ H.powerset, (if S = ∅ then (1 : ℝ) else 0) = 1 := by
    rw [sum_ite_eq' H.powerset ∅ (fun _ => (1 : ℝ))]
    simp
  rw [hval] at hsum
  have := hsum.const_mul ((1 / 2) ^ H.card)
  rwa [mul_one] at this

/-- Full Chowla (any weights) gives every sign pattern its expected density. -/
theorem tendsto_pattern_of_chowla (w : ℕ → ℝ) (hw : ∀ n, 0 < n → 0 < w n) (hC : Chowla w)
    (H : Finset ℕ) {ε : ℕ → ℝ} (hε : IsSignVec H ε) :
    Tendsto (wavg w (patternInd H ε)) atTop (𝓝 ((1 / 2) ^ H.card)) :=
  tendsto_pattern w hw H hε fun S _ hS => hC S.card (card_pos.mpr hS) S rfl

theorem natW_pos : ∀ n, 0 < n → 0 < natW n := fun _ _ => by simp [natW]

theorem logW_pos : ∀ n, 0 < n → 0 < logW n := fun n hn => by
  simp only [logW]; exact one_div_pos.mpr (by exact_mod_cast hn)

/-! ### Cited unconditional theorems, used as named hypotheses -/

/-- Tao (Forum Math. Pi 2016): the logarithmically averaged two-point Chowla conjecture. -/
def TaoTwoPoint : Prop := ChowlaOrder logW 2

/-- Tao–Teräväinen (Duke 2019; J. Théor. Nombres Bordeaux 2018): the logarithmically
averaged Chowla conjecture for every odd order. -/
def TaoTeravainenOdd : Prop := ∀ k : ℕ, Odd k → ChowlaOrder logW k

/-- **Length ≤ 3 sign patterns, logarithmic density.**  From the two cited theorems,
every sign pattern of length at most three occurs with logarithmic density `2^{-k}`. -/
theorem logPattern_le_three (hT : TaoTwoPoint) (hTT : TaoTeravainenOdd)
    (H : Finset ℕ) (hH : H.card ≤ 3) {ε : ℕ → ℝ} (hε : IsSignVec H ε) :
    Tendsto (wavg logW (patternInd H ε)) atTop (𝓝 ((1 / 2) ^ H.card)) := by
  refine tendsto_pattern logW logW_pos H hε fun S hS hne => ?_
  have h1 : 1 ≤ S.card := card_pos.mpr hne
  have h3 : S.card ≤ 3 := (card_le_card hS).trans hH
  interval_cases hc : S.card
  · exact hTT 1 odd_one S hc
  · exact hT S hc
  · exact hTT 3 (by decide) S hc

/-- Under Littlewood's form of RH, each single sign `λ(n + h) = ±1` has natural density 1/2. -/
theorem natPattern_one_of_littlewoodRH (hRH : LittlewoodRH) (h : ℕ) {e : ℝ}
    (he : e = 1 ∨ e = -1) :
    Tendsto (wavg natW (patternInd {h} (fun _ => e))) atTop (𝓝 (1 / 2)) := by
  have := tendsto_pattern natW natW_pos {h} (ε := fun _ => e)
    (fun _ _ => he) fun S hS hne => by
      have : S = {h} := (subset_singleton_iff.mp hS).resolve_left (nonempty_iff_ne_empty.mp hne)
      subst this
      exact chowlaOrder_one_of_littlewoodRH hRH {h} (card_singleton h)
  simpa using this

end ChowlaRH
