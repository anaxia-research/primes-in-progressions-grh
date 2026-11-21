/-
From a power bound for the Mertens function to the same power bound for the
summatory Liouville function.

`L(N) = ∑_{a ≤ N} σ(a) M(N / a) = ∑_{d² ≤ N} M(N / d²)`, and for `θ > 1/2`
the bound `|M(N)| ≤ C N^θ` gives `|L(N)| ≤ C ζ(2θ) N^θ`.
-/
import ChowlaRH.SquareKernel

open ArithmeticFunction Finset Real

namespace ChowlaRH

/-- The Mertens function `M(N) = ∑_{1 ≤ n ≤ N} μ(n)`. -/
def mertens (N : ℕ) : ℤ := ∑ n ∈ Ioc 0 N, moebius n

/-- The summatory Liouville function `L(N) = ∑_{1 ≤ n ≤ N} λ(n)`. -/
def summatoryLiouville (N : ℕ) : ℤ := ∑ n ∈ Ioc 0 N, liouville n

/-- `|M(N)| ≤ C N^θ` for all `N`. -/
def MertensBound (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, |(mertens N : ℝ)| ≤ C * (N : ℝ) ^ θ

/-- `|L(N)| ≤ C N^θ` for all `N`. -/
def LiouvilleBound (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, |(summatoryLiouville N : ℝ)| ≤ C * (N : ℝ) ^ θ

/-- Littlewood's form of the Riemann hypothesis: `M(N) ≪_ε N^{1/2+ε}` for every `ε > 0`.
Classically this is equivalent to RH (Littlewood 1912; Titchmarsh, Thm 14.25(C)).
It is used here only as an explicit hypothesis. -/
def LittlewoodRH : Prop := ∀ ε : ℝ, 0 < ε → MertensBound (1 / 2 + ε)

theorem summatoryLiouville_eq (N : ℕ) :
    summatoryLiouville N = ∑ a ∈ Ioc 0 N, sqKernel a * mertens (N / a) := by
  rw [summatoryLiouville, liouville_eq_sqKernel_mul_moebius, sum_Ioc_mul_eq_sum_sum]
  rfl

theorem mertens_one : mertens 1 = 1 := by
  simp [mertens]

/-- The transfer theorem: a Mertens bound with exponent `θ > 1/2` gives a Liouville
bound with the same exponent. -/
theorem liouvilleBound_of_mertensBound {θ : ℝ} (hθ : 1 / 2 < θ) (h : MertensBound θ) :
    LiouvilleBound θ := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := hC 1
    simp [mertens_one] at this
    linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hsum : Summable fun d : ℕ => ((d : ℝ) ^ (2 * θ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  set S := ∑' d : ℕ, ((d : ℝ) ^ (2 * θ))⁻¹
  refine ⟨C * S, fun N => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- the summand that bounds a term with `a` a square
  set f : ℕ → ℝ := fun a => C * ((N : ℝ) / a) ^ θ with hf
  have hf0 : ∀ a, 0 ≤ f a := fun a => mul_nonneg hC0 (rpow_nonneg (by positivity) _)
  rw [summatoryLiouville_eq]
  push_cast
  calc |∑ a ∈ Ioc 0 N, (sqKernel a : ℝ) * (mertens (N / a) : ℝ)|
      ≤ ∑ a ∈ Ioc 0 N, |(sqKernel a : ℝ) * (mertens (N / a) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc 0 N, (if IsSquare a then f a else 0) := by
        refine sum_le_sum fun a _ => ?_
        obtain ⟨h01, hsq⟩ := sqKernel_spec a
        by_cases ha : sqKernel a = 0
        · simp only [ha, Int.cast_zero, zero_mul, abs_zero]
          split_ifs
          · exact hf0 a
          · exact le_refl 0
        · have h1 : sqKernel a = 1 := h01.resolve_left ha
          rw [ite_eq_left_iff.mpr (fun h => absurd (hsq ha) h), h1, Int.cast_one, one_mul]
          refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
          exact rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hθ0
    _ = ∑ a ∈ (Ioc 0 N).filter IsSquare, f a := (sum_filter _ _).symm
    _ ≤ ∑ a ∈ (Ioc 0 N).image (fun d => d * d), f a := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => hf0 a)
        intro a ha
        simp only [mem_filter, mem_Ioc] at ha
        obtain ⟨⟨ha0, haN⟩, r, rfl⟩ := ha
        refine mem_image.mpr ⟨r, mem_Ioc.mpr ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos r with hr | hr
          · simp [hr] at ha0
          · exact hr
        · exact le_trans (Nat.le_mul_self r) haN
    _ = ∑ d ∈ Ioc 0 N, f (d * d) := by
        rw [sum_image]
        intro x _ y _ hxy
        exact Nat.mul_self_inj.mp hxy
    _ = C * (N : ℝ) ^ θ * ∑ d ∈ Ioc 0 N, ((d : ℝ) ^ (2 * θ))⁻¹ := by
        rw [mul_sum]
        refine sum_congr rfl fun d hd => ?_
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
        simp only [hf]
        push_cast
        rw [div_rpow hN0 (by positivity), rpow_mul hd0.le]
        rw [show ((d : ℝ) * d) = (d : ℝ) ^ (2 : ℝ) by rw [rpow_two]; ring]
        field_simp
    _ ≤ C * (N : ℝ) ^ θ * S := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (rpow_nonneg hN0 _))
        exact hsum.sum_le_tsum _ (fun d _ => by positivity)
    _ = C * S * (N : ℝ) ^ θ := by ring

/-- Under Littlewood's form of RH, `L(N) ≪_ε N^{1/2+ε}` for every `ε > 0`. -/
theorem liouvilleBound_of_littlewoodRH (hRH : LittlewoodRH) :
    ∀ ε : ℝ, 0 < ε → LiouvilleBound (1 / 2 + ε) := fun ε hε =>
  liouvilleBound_of_mertensBound (by linarith) (hRH ε hε)

end ChowlaRH
