import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet

open Complex

-- The object we're trying to show doesn't exist.
structure BadChar (N : ℕ) [NeZero N] where
  χ : DirichletCharacter ℂ N
  χ_ne : χ ≠ 1
  χ_sq : χ ^ 2 = 1
  hχ : χ.LFunction 1 = 0

variable {N : ℕ} [NeZero N]

noncomputable section

lemma BadChar.χ_apply_eq (B : BadChar N) (x : ZMod N) :
    B.χ x = 0 ∨ B.χ x = 1 ∨ B.χ x = -1 := by
  by_cases hx : IsUnit x
  · have hx' : (B.χ x) ^ 2 = 1 := by
      rw [← B.χ.pow_apply' two_ne_zero, B.χ_sq, MulChar.one_apply hx]
    rw [sq_eq_one_iff] at hx'
    tauto
  · simp only [B.χ.map_nonunit hx, true_or]

/-- The real-valued character whose coercion to `ℂ` is `B.χ`. -/
def BadChar.χ₀ (B : BadChar N) : DirichletCharacter ℝ N :=
  { toFun := fun x ↦ (B.χ x).re,
    map_one' := by simp only [map_one, one_re],
    map_mul' := by
      intro x y
      rcases B.χ_apply_eq x with hx | hx | hx <;>
      rcases B.χ_apply_eq y with hy | hy | hy <;>
      simp only [hx, hy, map_mul, mul_neg, mul_one, neg_zero, zero_re, neg_re, one_re, mul_zero]
    map_nonunit' := by
      intro u hu
      simp only [B.χ.map_nonunit hu, zero_re] }

lemma BadChar.χ₀_def (B : BadChar N) : B.χ = B.χ₀.ringHomComp ofRealHom := by
  ext a
  rcases B.χ_apply_eq a with ha | ha | ha <;>
  simp only [ha, MulChar.ringHomComp_apply, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    zero_re, neg_re, one_re, ofRealHom_eq_coe, ofReal_zero, ofReal_one, ofReal_neg, BadChar.χ₀]

/-- The auxiliary function `s ↦ ζ s * L B.χ s`. -/
def BadChar.F (B : BadChar N) : ℂ → ℂ := Function.update
  (fun s : ℂ ↦ riemannZeta s * B.χ.LFunction s) 1 (deriv B.χ.LFunction 1)

lemma BadChar.F_differentiableAt_of_ne (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (B.F) s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_riemannZeta hs).mul <|
      B.χ.differentiableAt_LFunction s (.inl hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht using Function.update_noteq ht ..

lemma BadChar.F_differentiable (B : BadChar N) : Differentiable ℂ B.F := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact B.F_differentiableAt_of_ne hs
  · apply AnalyticAt.differentiableAt
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact B.F_differentiableAt_of_ne ht
    -- now reduced to showing *continuity* at s = 1
    let G : ℂ → ℂ := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
    let H : ℂ → ℂ := Function.update
      (fun s ↦ B.χ.LFunction s / (s - 1)) 1 (deriv B.χ.LFunction 1)
    have : B.F = G * H := by
      ext t
      rcases eq_or_ne t 1 with rfl | ht
      · simp only [F, G, H, Pi.mul_apply, one_mul, Function.update_same]
      · simp only [F, G, H, Pi.mul_apply, Function.update_noteq ht]
        field_simp [sub_ne_zero.mpr ht]
        ring
    rw [this]
    apply ContinuousAt.mul
    · simpa only [G, continuousAt_update_same] using riemannZeta_residue_one
    · have : HasDerivAt (B.χ.LFunction) (deriv B.χ.LFunction 1) 1 := by
        apply DifferentiableAt.hasDerivAt
        refine DirichletCharacter.differentiableAt_LFunction B.χ 1 (.inr B.χ_ne)
      rw [hasDerivAt_iff_tendsto_slope] at this
      simp only [funext (slope_def_field B.χ.LFunction 1),
        B.hχ, sub_zero] at this
      rw [Metric.continuousAt_iff']
      intro ε hε
      simp only [Metric.tendsto_nhds, eventually_nhdsWithin_iff] at this
      filter_upwards [this ε hε] with a ha
      rcases eq_or_ne a 1 with rfl | ha'
      · simp only [dist_self, hε]
      · simpa only [H, Function.update_noteq ha', Function.update_same] using ha ha'

lemma BadChar.F_neg_two (B : BadChar N) : B.F (-2) = 0 := by
  simp only [BadChar.F]
  have := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at this
  rw [Function.update_noteq (mod_cast (by omega : (-2 : ℤ) ≠ 1)), this, zero_mul]

/-- The real-valued arithmetic function whose L-series is `B.F`. -/
def BadChar.e (B : BadChar N) : ArithmeticFunction ℝ := .zeta * (toArithmeticFunction (B.χ₀ ·))

lemma BadChar.F_eq_LSeries (B : BadChar N) {s : ℂ} (hs : 1 < s.re) :
    B.F s = LSeries (B.e ·) s := by
  have (n : ℕ) : (B.e n : ℂ) = LSeries.convolution (fun _ ↦ 1) (B.χ ·) n := by
    simp only [e, ArithmeticFunction.mul_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, ite_mul, zero_mul,
      one_mul, ofReal_sum, χ₀_def, MulChar.ringHomComp_apply, ofRealHom_eq_coe,
      LSeries.convolution_def]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [(Nat.ne_zero_of_mem_divisorsAntidiagonal hi).1, ↓reduceIte, toArithmeticFunction,
      ArithmeticFunction.coe_mk, (Nat.ne_zero_of_mem_divisorsAntidiagonal hi).2]
  simp only [this]
  rw [LSeries_convolution', BadChar.F, Function.update_noteq]
  · congr 1
    exact (LSeriesHasSum_one hs).LSeries_eq.symm
    exact DirichletCharacter.LFunction_eq_LSeries _ hs
  · intro h
    simp only [h, one_re, lt_self_iff_false] at hs
  · rwa [← Pi.one_def, LSeriesSummable_one_iff]
  · exact ZMod.LSeriesSummable_of_one_lt_re _ hs

lemma BadChar.mult_e (B : BadChar N) : B.e.IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_zeta.natCast.mul
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, one_ne_zero, ↓reduceIte,
      Nat.cast_one, map_one]
  · intro m n hm hn _
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, mul_eq_zero, hm, hn, false_or,
      if_false, Nat.cast_mul, map_mul]

lemma BadChar.e_prime_pow (B : BadChar N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ B.e (p ^ k) := by
  simp only [e, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk, Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq,
    false_and, ↓reduceIte, Nat.cast_pow, map_pow]
  have := B.χ_apply_eq p
  simp only [B.χ₀_def, MulChar.ringHomComp_apply, ofRealHom_eq_coe, ofReal_eq_zero,
    ← neg_eq_iff_eq_neg (b := (1 : ℂ)), ← ofReal_neg, neg_eq_iff_eq_neg (b := (1 : ℝ)),
    ofReal_eq_one] at this
  rcases this with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

lemma BadChar.e_nonneg (B : BadChar N) (n : ℕ) : 0 ≤ B.e n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [B.mult_e.multiplicative_factorization _ hn] using
      Finset.prod_nonneg fun p hp ↦ B.e_prime_pow (Nat.prime_of_mem_primeFactors hp) _

open scoped ComplexOrder

lemma derivs_from_coeffs (a : ArithmeticFunction ℂ) (h1 : 1 < a 1) (hn : ∀ n, 2 ≤ n → 0 ≤ a n)
  (x : ℝ) (h : LSeriesSummable a x) (n : ℕ) :  0 ≤ (-1) ^ n * iteratedDeriv n (LSeries a) x := by

  sorry



/-- The goal: bad characters do not exist. -/
theorem BadChar.elim (B : BadChar N) : False :=
  sorry
