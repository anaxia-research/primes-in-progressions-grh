import LiouvilleEnergyRH.Progressions.ChiPsi
import LiouvilleEnergyRH.PrimeCount.Theta

/-!
# Primes in arithmetic progressions under Hypothesis H

* `psiAP_bound`: `|φ(q) ψ(x; q, a) - x| ≤ K q^{1 + η} x^{1/2 + η}` for `a` coprime to `q`;
* `least_prime_in_AP`: the least prime `p ≡ a (mod q)` is at most `C q^{2 + δ}`.
-/

namespace LiouvilleEnergyRH.Progressions

open Complex Finset ArithmeticFunction Classical
open scoped LSeries.notation

/-- `ψ(x; q, a) = ∑_{n ≤ x, n ≡ a} Λ(n)`. -/
noncomputable def psiAP (q : ℕ) (a : ZMod q) (x : ℝ) : ℝ :=
  ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), vonMangoldt n

/-- The prime powers sharing a factor with `q` contribute at most `log q + 2 √x log x`. -/
lemma nonunit_sum_le {q : ℕ} (hq : q ≠ 0) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (if IsUnit (n : ZMod q) then 0 else vonMangoldt n) ≤
      Real.log q + 2 * √x * Real.log x := by
  have hpt : ∀ n ∈ Ioc 0 ⌊x⌋₊, (if IsUnit (n : ZMod q) then 0 else vonMangoldt n) ≤
      (if n.Prime ∧ ¬IsUnit (n : ZMod q) then vonMangoldt n else 0) +
        (if ¬n.Prime then vonMangoldt n else 0) := by
    intro n _
    have h0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
    by_cases hu : IsUnit (n : ZMod q) <;> by_cases hp : n.Prime <;> simp [hu, hp, h0]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have h2 : ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬n.Prime), vonMangoldt n ≤ 2 * √x * Real.log x := by
    rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Chebyshev.psi_sub_theta_le hx
  have h1 : ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => n.Prime ∧ ¬IsUnit (n : ZMod q)), vonMangoldt n ≤
      Real.log q := by
    calc ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => n.Prime ∧ ¬IsUnit (n : ZMod q)), vonMangoldt n
        ≤ ∑ p ∈ q.primeFactors, vonMangoldt p := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [mem_filter] at hn
            obtain ⟨-, hp, hu⟩ := hn
            rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp, not_not] at hu
            exact Nat.mem_primeFactors.mpr ⟨hp, hu, hq⟩
          · intro n _ _; exact vonMangoldt_nonneg
      _ = ∑ p ∈ q.primeFactors, Real.log p := by
          refine sum_congr rfl (fun p hp => ?_)
          exact vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp)
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log q := by
          apply Real.log_le_log
          · apply prod_pos; intro p hp
            exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  linarith

/-- **Orthogonality.** `φ(q) ψ(x; q, a) = ∑_χ χ(a)⁻¹ ∑_{n ≤ x} χ(n) Λ(n)`. -/
lemma ortho {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (x : ℝ) :
    (q.totient : ℂ) * (psiAP q a x : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ∑ n ∈ Ioc 0 ⌊x⌋₊, coef χ n := by
  simp only [coef, Pi.mul_apply, mul_sum]
  rw [sum_comm]
  have hn : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ (n : ZMod q) * (vonMangoldt n : ℂ)) =
      (if a = (n : ZMod q) then (q.totient : ℂ) else 0) * (vonMangoldt n : ℂ) := by
    intro n
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q), sum_mul]
    refine sum_congr rfl (fun χ _ => by ring)
  simp only [hn, psiAP]
  push_cast
  rw [mul_sum, sum_filter]
  refine sum_congr rfl (fun n _ => ?_)
  by_cases h : a = (n : ZMod q)
  · simp [h]
  · have h' : ¬((n : ZMod q) = a) := fun e => h e.symm
    simp [h, h']

lemma one_inv_apply {q : ℕ} {a : ZMod q} (ha : IsUnit a) :
    (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [ZMod.inv_coe_unit]
  exact MulChar.one_apply (u⁻¹).isUnit

/-- The principal character picks out the `n` coprime to `q`. -/
lemma sum_coef_one {q : ℕ} (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, coef (1 : DirichletCharacter ℂ q) n =
      ((∑ n ∈ Ioc 0 ⌊x⌋₊, (if IsUnit (n : ZMod q) then vonMangoldt n else 0) : ℝ) : ℂ) := by
  push_cast
  refine sum_congr rfl (fun n _ => ?_)
  simp only [coef, Pi.mul_apply]
  by_cases hu : IsUnit (n : ZMod q)
  · simp [hu, MulChar.one_apply hu]
  · simp [hu, MulChar.map_nonunit _ hu]

/-- **Primes in progressions.** Under Hypothesis H,
`|φ(q) ψ(x; q, a) - x| ≤ K q^{1 + η} x^{1/2 + η}` for `a` coprime to `q` and `x ≥ 1`. -/
theorem psiAP_bound (h : HypothesisH) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ x : ℝ, 1 ≤ x →
      |(q.totient : ℝ) * psiAP q a x - x| ≤ K * (q : ℝ) ^ (1 + η) * x ^ (1 / 2 + η) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := chi_psi_bound h hη
  have hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hs1
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [DirichletCharacter.LFunction_modOne_eq] at this
  obtain ⟨K₂, hK₂⟩ := PrimeCount.psi_bound hz hη
  refine ⟨K₁ + 1 + 2 / η + |K₂|, by positivity, ?_⟩
  intro q _ a ha x hx
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq0
  have hx0 : 0 < x := by linarith
  set X := x ^ (1 / 2 + η) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hx (by linarith)
  set Q := (q : ℝ) ^ (1 + η) with hQ
  have hQq : (q : ℝ) ≤ Q := by
    calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Q := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hQ1 : 1 ≤ Q := hq.trans hQq
  -- the non-principal characters
  set S1 : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, (if IsUnit (n : ZMod q) then vonMangoldt n else 0) with hS1
  have hdecomp := ortho ha x
  rw [← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)), one_inv_apply ha, one_mul,
    sum_coef_one] at hdecomp
  have hrest : ‖∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
      χ a⁻¹ * ∑ n ∈ Ioc 0 ⌊x⌋₊, coef χ n‖ ≤ q * (K₁ * (q : ℝ) ^ η * X) := by
    calc _ ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
          ‖χ a⁻¹ * ∑ n ∈ Ioc 0 ⌊x⌋₊, coef χ n‖ := norm_sum_le _ _
      _ ≤ ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), K₁ * (q : ℝ) ^ η * X := by
          refine sum_le_sum (fun χ hχ => ?_)
          have hχ1 : χ ≠ 1 := ne_of_mem_erase hχ
          rw [norm_mul]
          calc ‖χ a⁻¹‖ * ‖∑ n ∈ Ioc 0 ⌊x⌋₊, coef χ n‖
              ≤ 1 * (K₁ * (q : ℝ) ^ η * X) :=
                mul_le_mul (DirichletCharacter.norm_le_one χ _) (hK₁ q χ hχ1 x hx)
                  (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = (univ.erase (1 : DirichletCharacter ℂ q)).card * (K₁ * (q : ℝ) ^ η * X) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ q * (K₁ * (q : ℝ) ^ η * X) := by
          gcongr
          have h1 : (univ.erase (1 : DirichletCharacter ℂ q)).card ≤
              (univ : Finset (DirichletCharacter ℂ q)).card := card_erase_le
          have h2 : (univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
            rw [card_univ, ← Nat.card_eq_fintype_card,
              DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
          exact_mod_cast h1.trans (h2 ▸ Nat.totient_le q)
  have hdiff1 : |(q.totient : ℝ) * psiAP q a x - S1| ≤ q * (K₁ * (q : ℝ) ^ η * X) := by
    have : (((q.totient : ℝ) * psiAP q a x - S1 : ℝ) : ℂ) =
        ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ a⁻¹ * ∑ n ∈ Ioc 0 ⌊x⌋₊, coef χ n := by
      rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast, hdecomp, hS1]; ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, this]
    exact hrest
  -- ψ(x) - S1 is the non-unit part
  have hS1ψ : Chebyshev.psi x - S1 =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (if IsUnit (n : ZMod q) then 0 else vonMangoldt n) := by
    rw [hS1, Chebyshev.psi, ← sum_sub_distrib]
    refine sum_congr rfl (fun n _ => ?_)
    split_ifs <;> ring
  have hnon := nonunit_sum_le hq0 hx
  have hnon0 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (if IsUnit (n : ZMod q) then 0 else vonMangoldt n) :=
    sum_nonneg (fun n _ => by split_ifs <;> simp [vonMangoldt_nonneg])
  have hψ : |Chebyshev.psi x - x| ≤ K₂ * X := hK₂ x hx
  have hsl : √x * Real.log x ≤ 1 / η * X := PrimeCount.sqrt_mul_log_le hx hη
  have hlogq : Real.log q ≤ q := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hmain1 : q * (K₁ * (q : ℝ) ^ η * X) = K₁ * Q * X := by
    rw [hQ, Real.rpow_add (by linarith), Real.rpow_one]; ring
  have hK₂' : |K₂ * X| ≤ |K₂| * Q * X := by
    rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < X)]
    calc |K₂| * X = |K₂| * 1 * X := by ring
      _ ≤ |K₂| * Q * X := by gcongr
  have hQX : 1 ≤ Q * X := one_le_mul_of_one_le_of_one_le hQ1 hX1
  have hlogq' : Real.log q ≤ Q * X := by
    have : Q * 1 ≤ Q * X := mul_le_mul_of_nonneg_left hX1 (by linarith)
    linarith
  have hsl' : 2 * √x * Real.log x ≤ 2 / η * Q * X := by
    have : 2 * (√x * Real.log x) ≤ 2 * (1 / η * X) := by linarith
    have h2 : 2 * (1 / η * X) ≤ 2 / η * Q * X := by
      calc 2 * (1 / η * X) = 2 / η * 1 * X := by ring
        _ ≤ 2 / η * Q * X := by gcongr
    linarith
  have hk1 : K₂ * X ≤ |K₂| * Q * X := (le_abs_self _).trans hK₂'
  have hk2 : -(|K₂| * Q * X) ≤ K₂ * X := by have := neg_abs_le (K₂ * X); linarith
  have hT : (K₁ + 1 + 2 / η + |K₂|) * Q * X =
      K₁ * Q * X + Q * X + 2 / η * Q * X + |K₂| * Q * X := by ring
  have hn1 : Chebyshev.psi x - S1 ≤ Real.log q + 2 * √x * Real.log x := by
    rw [hS1ψ]; convert hnon using 1; exact sum_congr rfl (fun n _ => by congr 1)
  have hn0 : 0 ≤ Chebyshev.psi x - S1 := by rw [hS1ψ]; exact hnon0
  clear_value S1
  rw [hmain1] at hdiff1
  rw [abs_le] at hdiff1 hψ ⊢
  rw [hT]
  constructor <;> linarith

/-- **The least prime in a progression (Linnik's constant 2 + δ).** Under Hypothesis H, for every
`δ ∈ (0, 1]` there is `C` such that for every `q ≥ 1` and every `a` coprime to `q` there is a
prime `p ≡ a (mod q)` with `p ≤ C q^{2 + δ}`. -/
theorem least_prime_in_AP (h : HypothesisH) {dl : ℝ} (hdl : 0 < dl) (hdl1 : dl ≤ 1) :
    ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (a : ℕ), a.Coprime q →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ C * (q : ℝ) ^ (2 + dl) := by
  set η := dl / 20 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨K, hK0, hK⟩ := psiAP_bound h hη0
  set M := K + 2 / η with hM
  have hM0 : 0 ≤ M := by positivity
  set r : ℝ := 1 / 2 - η with hr
  have hr0 : 0 < r := by rw [hr, hη]; linarith
  set C : ℝ := (M + 1) ^ (1 / r) with hC
  have hC1 : 1 ≤ C := Real.one_le_rpow (by linarith) (by positivity)
  have hCr : C ^ r = M + 1 := by
    rw [hC, ← Real.rpow_mul (by linarith), one_div_mul_cancel hr0.ne', Real.rpow_one]
  refine ⟨C, fun q _ a ha => ?_⟩
  by_contra hno
  push Not at hno
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq0
  set x : ℝ := C * (q : ℝ) ^ (2 + dl) with hx
  have hqd : 1 ≤ (q : ℝ) ^ (2 + dl) := Real.one_le_rpow hq (by linarith)
  have hx1 : 1 ≤ x := one_le_mul_of_one_le_of_one_le hC1 hqd
  have hx0 : 0 < x := by linarith
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  -- without such primes, ψ(x; q, a) only sees prime powers
  have hsub : (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q)) ⊆
      (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬n.Prime) := by
    intro n hn
    simp only [mem_filter] at hn ⊢
    refine ⟨hn.1, fun hp => ?_⟩
    have hmod : n ≡ a [MOD q] := (ZMod.natCast_eq_natCast_iff n a q).mp hn.2
    have hlt := hno n hp hmod
    have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp (mem_Ioc.mp hn.1).2
    linarith
  have hpsiAP : psiAP q (a : ZMod q) x ≤ 2 * √x * Real.log x := by
    calc psiAP q (a : ZMod q) x
        ≤ ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ¬n.Prime), vonMangoldt n :=
          sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => vonMangoldt_nonneg)
      _ = Chebyshev.psi x - Chebyshev.theta x := (Chebyshev.psi_sub_theta_eq_sum_not_prime x).symm
      _ ≤ 2 * √x * Real.log x := Chebyshev.psi_sub_theta_le hx1
  have hpsiAP0 : 0 ≤ psiAP q (a : ZMod q) x := sum_nonneg (fun n _ => vonMangoldt_nonneg)
  set X := x ^ (1 / 2 + η) with hX
  set Q := (q : ℝ) ^ (1 + η) with hQ
  have hX0 : 0 < X := by positivity
  have hQq : (q : ℝ) ≤ Q := by
    calc (q : ℝ) = (q : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Q := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hsl : √x * Real.log x ≤ 1 / η * X := PrimeCount.sqrt_mul_log_le hx1 hη0
  have hb := hK q (a : ZMod q) hu x hx1
  have htot : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφψ : (q.totient : ℝ) * psiAP q (a : ZMod q) x ≤ 2 / η * Q * X := by
    have hsl0 : 0 ≤ √x * Real.log x := mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hx1)
    calc (q.totient : ℝ) * psiAP q (a : ZMod q) x ≤ q * (2 * √x * Real.log x) :=
          mul_le_mul htot hpsiAP hpsiAP0 (by linarith)
      _ = 2 * q * (√x * Real.log x) := by ring
      _ ≤ 2 * Q * (1 / η * X) := by gcongr
      _ = 2 / η * Q * X := by ring
  have hxle : x ≤ M * Q * X := by
    rw [abs_le] at hb
    have : M * Q * X = K * Q * X + 2 / η * Q * X := by rw [hM]; ring
    linarith [hb.1]
  -- x = x^{1/2 + η} x^{r}
  have hsplit : x = X * x ^ r := by
    rw [hX, ← Real.rpow_add hx0, hr]; ring_nf; exact (Real.rpow_one x).symm
  have hxr : x ^ r ≤ M * Q := by
    have : X * x ^ r ≤ X * (M * Q) := by rw [← hsplit]; linarith
    exact le_of_mul_le_mul_left this hX0
  have hxr' : x ^ r = (M + 1) * (q : ℝ) ^ ((2 + dl) * r) := by
    rw [hx, Real.mul_rpow (by linarith) (by positivity), hCr, ← Real.rpow_mul (by linarith)]
  have hexp : 1 + η ≤ (2 + dl) * r := by rw [hr, hη]; nlinarith
  have hqq : Q ≤ (q : ℝ) ^ ((2 + dl) * r) := Real.rpow_le_rpow_of_exponent_le hq hexp
  have hQ0 : 0 < Q := by positivity
  rw [hxr'] at hxr
  nlinarith

end LiouvilleEnergyRH.Progressions
