import LiouvilleEnergyRH.Closure
import LiouvilleEnergyRH.Mertens.Main
import ChowlaRH

/-!
# The averaged Chowla conjecture under Hypothesis H

Hypothesis H (no Dirichlet `L`-function vanishes in `re s > 1/2`) gives, for every `ε > 0`,

* `M(N) = ∑_{n ≤ N} μ(n) ≪_ε N^{1/2 + ε}` (`littlewoodRH_of_H`);
* `L(N) = ∑_{n ≤ N} λ(n) ≪_ε N^{1/2 + ε}` (`liouvilleBound_of_H`);
* `∑_{n ≤ N} λ(n + h) ≪_ε (N + h)^{1/2 + ε}` uniformly in the shift `h` (`shifted_sum_bound`);
* the one-point Chowla conjecture with natural averaging for every shift (`chowla_one_of_H`),
  and natural density `1/2` for each sign of `λ(n + h)` (`sign_density_of_H`).

The analytic input is `LiouvilleEnergyRH.Mertens.mertens_bound`; the arithmetic transfer from
`M` to `L` is `ChowlaRH.liouvilleBound_of_mertensBound`.
-/

namespace LiouvilleEnergyRH

open ArithmeticFunction Finset ChowlaRH
open scoped ArithmeticFunction.Moebius

/-- Hypothesis H contains the zero-free half-plane for `ζ`. -/
theorem zeta_ne_zero_of_H (h : HypothesisH) :
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
  rwa [DirichletCharacter.LFunction_modOne_eq] at this

/-- **Littlewood's bound for the Mertens function.** Hypothesis H implies
`|M(N)| ≤ C N^{1/2 + ε}` for every `ε > 0`. -/
theorem littlewoodRH_of_H (h : HypothesisH) : LittlewoodRH := by
  intro ε hε
  obtain ⟨K, hK⟩ := Mertens.mertens_bound (zeta_ne_zero_of_H h) hε
  refine ⟨max K 0, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [mertens, Ioc_self, sum_empty, Int.cast_zero, abs_zero, Nat.cast_zero]
    exact mul_nonneg (le_max_right _ _) (by positivity)
  · have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := hK N hx
    rw [Nat.floor_natCast] at hb
    have hcast : ‖∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ)‖ = |(mertens N : ℝ)| := by
      rw [mertens, ← Complex.norm_intCast]
      push_cast
      rfl
    have hp : 0 ≤ (N : ℝ) ^ (1 / 2 + ε) := by positivity
    calc |(mertens N : ℝ)| = ‖∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℂ)‖ := hcast.symm
      _ ≤ K * (N : ℝ) ^ (1 / 2 + ε) := hb
      _ ≤ max K 0 * (N : ℝ) ^ (1 / 2 + ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp

/-- **The summatory Liouville function.** Hypothesis H implies `|L(N)| ≤ C N^{1/2 + ε}`. -/
theorem liouvilleBound_of_H (h : HypothesisH) (ε : ℝ) (hε : 0 < ε) :
    LiouvilleBound (1 / 2 + ε) :=
  liouvilleBound_of_littlewoodRH (littlewoodRH_of_H h) ε hε

/-- **Shifted sums, uniformly in the shift.** Under Hypothesis H, for every `ε > 0` there is `C`
with `|∑_{1 ≤ n ≤ N} λ(n + h)| ≤ C (N + h)^{1/2 + ε}` for all `N, h`. -/
theorem shifted_sum_bound (h : HypothesisH) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ k N : ℕ, |∑ n ∈ Ioc 0 N, lam (n + k)| ≤ C * ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC⟩ := liouvilleBound_of_H h ε hε
  refine ⟨2 * max C 0, fun k N => ?_⟩
  rw [sum_shift_eq]
  have hθ : 0 ≤ 1 / 2 + ε := by linarith
  have h1 := hC (N + k)
  have h2 := hC k
  have hmono : (k : ℝ) ^ (1 / 2 + ε) ≤ ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow (by positivity) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]) hθ
  have hp1 : 0 ≤ ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) := by positivity
  have hp2 : 0 ≤ (k : ℝ) ^ (1 / 2 + ε) := by positivity
  have hm : C ≤ max C 0 := le_max_left _ _
  have hm0 : 0 ≤ max C 0 := le_max_right _ _
  calc |(summatoryLiouville (N + k) : ℝ) - (summatoryLiouville k : ℝ)|
      ≤ |(summatoryLiouville (N + k) : ℝ)| + |(summatoryLiouville k : ℝ)| := abs_sub _ _
    _ ≤ C * ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) + C * (k : ℝ) ^ (1 / 2 + ε) := add_le_add h1 h2
    _ ≤ max C 0 * ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) + max C 0 * ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) := by
        gcongr
    _ = 2 * max C 0 * ((N + k : ℕ) : ℝ) ^ (1 / 2 + ε) := by ring

/-- **One-point Chowla.** Under Hypothesis H, `(1/N) ∑_{n ≤ N} λ(n + h) → 0` for every shift. -/
theorem chowla_one_of_H (h : HypothesisH) : ChowlaOrder natW 1 :=
  chowlaOrder_one_of_littlewoodRH (littlewoodRH_of_H h)

/-- **Signs of `λ`.** Under Hypothesis H, each value `λ(n + h) = ±1` has natural density `1/2`. -/
theorem sign_density_of_H (h : HypothesisH) (k : ℕ) {e : ℝ} (he : e = 1 ∨ e = -1) :
    Filter.Tendsto (wavg natW (patternInd {k} (fun _ => e))) Filter.atTop
      (nhds (1 / 2)) :=
  natPattern_one_of_littlewoodRH (littlewoodRH_of_H h) k he

/-! ### Two-point correlations averaged over the shift

For every `ε > 0` there is `C` with
`|∑_{1 ≤ h ≤ H} ∑_{1 ≤ n ≤ N} λ(n) λ(n + h)| ≤ C N (N + H)^{1/2 + ε}`; with `H = N` the double
sum is `O(N^{3/2 + ε})`, against the trivial bound `N^2`. -/

theorem abs_lam_le (n : ℕ) : |lam n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lam]
  · rcases lam_eq_or hn.ne' with h | h <;> simp [h]

/-- **Two-point correlations averaged over the shift.** -/
theorem two_point_shift_average (h : HypothesisH) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N H : ℕ,
      |∑ k ∈ Ioc 0 H, ∑ n ∈ Ioc 0 N, lam n * lam (n + k)|
        ≤ C * N * ((N + H : ℕ) : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC⟩ := shifted_sum_bound h ε hε
  refine ⟨max C 0, le_max_right _ _, fun N H => ?_⟩
  have hθ : 0 ≤ 1 / 2 + ε := by linarith
  rw [Finset.sum_comm]
  have hterm : ∀ n ∈ Ioc 0 N,
      |∑ k ∈ Ioc 0 H, lam n * lam (n + k)| ≤ max C 0 * ((N + H : ℕ) : ℝ) ^ (1 / 2 + ε) := by
    intro n hn
    have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
    rw [← Finset.mul_sum, abs_mul]
    have hs : |∑ k ∈ Ioc 0 H, lam (n + k)| ≤ C * ((H + n : ℕ) : ℝ) ^ (1 / 2 + ε) := by
      have := hC n H
      simpa [add_comm] using this
    have hmono : ((H + n : ℕ) : ℝ) ^ (1 / 2 + ε) ≤ ((N + H : ℕ) : ℝ) ^ (1 / 2 + ε) :=
      Real.rpow_le_rpow (by positivity) (by push_cast; exact_mod_cast (by omega : H + n ≤ N + H)) hθ
    have hp : 0 ≤ ((H + n : ℕ) : ℝ) ^ (1 / 2 + ε) := by positivity
    calc |lam n| * |∑ k ∈ Ioc 0 H, lam (n + k)|
        ≤ 1 * |∑ k ∈ Ioc 0 H, lam (n + k)| :=
          mul_le_mul_of_nonneg_right (abs_lam_le n) (abs_nonneg _)
      _ ≤ C * ((H + n : ℕ) : ℝ) ^ (1 / 2 + ε) := by rw [one_mul]; exact hs
      _ ≤ max C 0 * ((H + n : ℕ) : ℝ) ^ (1 / 2 + ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp
      _ ≤ max C 0 * ((N + H : ℕ) : ℝ) ^ (1 / 2 + ε) :=
          mul_le_mul_of_nonneg_left hmono (le_max_right _ _)
  calc |∑ n ∈ Ioc 0 N, ∑ k ∈ Ioc 0 H, lam n * lam (n + k)|
      ≤ ∑ n ∈ Ioc 0 N, |∑ k ∈ Ioc 0 H, lam n * lam (n + k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, max C 0 * ((N + H : ℕ) : ℝ) ^ (1 / 2 + ε) := Finset.sum_le_sum hterm
    _ = max C 0 * N * ((N + H : ℕ) : ℝ) ^ (1 / 2 + ε) := by
        rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]; ring

/-- **Square averaging.** With `H = N`: `∑_{h ≤ N} ∑_{n ≤ N} λ(n)λ(n+h) = O(N^{3/2+ε})`. -/
theorem two_point_square_average (h : HypothesisH) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ N : ℕ,
      |∑ k ∈ Ioc 0 N, ∑ n ∈ Ioc 0 N, lam n * lam (n + k)|
        ≤ C * (N : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := two_point_shift_average h ε hε
  refine ⟨C * 2 ^ (1 / 2 + ε), fun N => ?_⟩
  have hb := hC N N
  have hθ : 0 ≤ 1 / 2 + ε := by linarith
  have h2N : ((N + N : ℕ) : ℝ) ^ (1 / 2 + ε) = 2 ^ (1 / 2 + ε) * (N : ℝ) ^ (1 / 2 + ε) := by
    rw [show ((N + N : ℕ) : ℝ) = 2 * N by push_cast; ring]
    exact Real.mul_rpow (by norm_num) (by positivity)
  have hpow : (N : ℝ) * (N : ℝ) ^ (1 / 2 + ε) = (N : ℝ) ^ (3 / 2 + ε) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp; rw [Real.zero_rpow (by linarith)]
    · rw [show (3 / 2 + ε) = 1 + (1 / 2 + ε) by ring,
        Real.rpow_add (x := (N : ℝ)) (by exact_mod_cast hN) 1 (1 / 2 + ε), Real.rpow_one]
  calc _ ≤ C * N * ((N + N : ℕ) : ℝ) ^ (1 / 2 + ε) := hb
    _ = C * 2 ^ (1 / 2 + ε) * ((N : ℝ) * (N : ℝ) ^ (1 / 2 + ε)) := by rw [h2N]; ring
    _ = C * 2 ^ (1 / 2 + ε) * (N : ℝ) ^ (3 / 2 + ε) := by rw [hpow]

end LiouvilleEnergyRH
