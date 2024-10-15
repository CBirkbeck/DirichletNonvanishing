import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Project.EulerProducts.Auxiliary

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
def BadChar.e (B : BadChar N) : ArithmeticFunction ℂ := .zeta * toArithmeticFunction (B.χ ·)

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

-- We use the ordering on `ℂ` given by comparing real parts for fixed imaginary part
open ComplexOrder

lemma BadChar.e_prime_pow (B : BadChar N) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ B.e (p ^ k) := by
  simp only [e, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk, Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq,
    false_and, ↓reduceIte, Nat.cast_pow, map_pow]
  rcases B.χ_apply_eq p with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp [h, le_refl, pow_nonneg]
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

lemma BadChar.e_one_eq_one (B : BadChar N) : B.e 1 = 1 := by
  simp only [e, toArithmeticFunction, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one,
    Prod.mk_one_one, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, Nat.cast_ite,
    CharP.cast_eq_zero, Nat.cast_one, ArithmeticFunction.coe_mk, mul_ite, mul_zero, ite_mul,
    zero_mul, one_mul, Finset.sum_singleton, Prod.snd_one, one_ne_zero, ↓reduceIte, Prod.fst_one,
    map_one]

open ArithmeticFunction in
open scoped LSeries.notation in
lemma BadChar.e_summable {s : ℂ} (hs : 1 < s.re) (B : BadChar N) : LSeriesSummable (B.e ·) s := by
  simp only [BadChar.e]
  have h₁ := LSeriesSummable_zeta_iff.mpr hs
  have h₂ := DirichletCharacter.LSeriesSummable_of_one_lt_re B.χ hs
  have h₂' : LSeriesSummable (toArithmeticFunction (↗B.χ)) s := by
    refine (LSeriesSummable_congr s fun {n} hn ↦ ?_).mp h₂
    simp only [χ₀_def, MulChar.ringHomComp_apply, ofRealHom_eq_coe, toArithmeticFunction, coe_mk,
      hn, ↓reduceIte]
  exact ArithmeticFunction.LSeriesSummable_mul h₁ h₂'

open scoped ComplexOrder

lemma derivs_from_coeffs (a : ArithmeticFunction ℂ) (hn : ∀ n, 0 ≤ a n) (x : ℝ)
    (h : LSeries.abscissaOfAbsConv (a ·) < x) (n : ℕ) :
    0 ≤ (-1) ^ n * iteratedDeriv n (LSeries (a ·)) x := by
  rw [LSeries_iteratedDeriv _ h]
  · rw [LSeries]
    ring_nf
    simp only [even_two, Even.mul_left, Even.neg_pow, one_pow, mul_one]
    apply tsum_nonneg
    intro k
    rw [LSeries.term_def]
    rcases eq_or_ne k 0 with rfl | hm
    · simp only [↓reduceIte, le_refl]
    · simp only [hm, ↓reduceIte]
      apply mul_nonneg
      · induction' n with n IH
        · simp only [Function.iterate_zero, id_eq]
          · exact hn k
        · rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
          apply mul_nonneg _ (IH)
          simp only [← natCast_log, zero_le_real, Real.log_natCast_nonneg]
      · simp only [le_def, zero_re, inv_re, zero_im, inv_im]
        constructor
        · apply div_nonneg _ (normSq_nonneg _)
          simp only [cpow_def, Nat.cast_eq_zero, hm, ↓reduceIte, ← natCast_log, ← ofReal_mul,
            exp_ofReal_re, Real.exp_nonneg]
        · simp only [cpow_def, Nat.cast_eq_zero, hm, ↓reduceIte, ← natCast_log, ← ofReal_mul,
          exp_ofReal_im, neg_zero, zero_div]

lemma BadChar.F_two_pos (B : BadChar N) : 0 < (B.F 2) := by
  rw [B.F_eq_LSeries (s := 2) (hs:= by norm_num), LSeries]
  apply tsum_pos (i := 1)
  · rw [LSeries.term_def]
    simp only [one_ne_zero, ↓reduceIte, e_one_eq_one, ofReal_one, Nat.cast_one, cpow_ofNat, one_pow,
      ne_eq, not_false_eq_true, div_self, zero_lt_one]
  · rw [← LSeriesSummable]
    apply BadChar.e_summable (by norm_num)
  · intro i
    rw [LSeries.term_def]
    simp only [cpow_ofNat]
    rcases eq_or_ne i 0 with rfl | hi
    · simp only [↓reduceIte, le_refl]
    · simp only [hi, ↓reduceIte]
      apply mul_nonneg
      · exact B.e_nonneg i
      · simp only [le_def, zero_re, inv_re, zero_im, inv_im]
        constructor
        · apply div_nonneg _ (normSq_nonneg _)
          norm_cast
          exact sq_nonneg i
        · norm_cast
          simp only [neg_zero, Nat.cast_pow, map_pow, normSq_natCast, zero_div]

lemma iteratedDeriv_comp_const_add (n : ℕ) (f : ℂ → ℂ) (s : ℂ) :
  iteratedDeriv n f s = iteratedDeriv n (fun z ↦ f (s + z)) 0 := by
  induction' n with n IH generalizing f
  · simp only [iteratedDeriv_zero, add_zero]
  · simp_rw [iteratedDeriv_succ']
    simp_rw [IH (deriv f), ← iteratedDerivWithin_univ ]
    apply iteratedDerivWithin_congr
    · exact uniqueDiffOn_univ
    · intro x _
      rw [deriv_comp_const_add]
    · simp only [Set.mem_univ]

lemma iteratedDeriv_eq_on_open (n : ℕ) {f g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (x : s)
    (hfg : Set.EqOn f g s) : iteratedDeriv n f x = iteratedDeriv n g x := by
  induction' n with n IH generalizing f g
  · simp only [iteratedDeriv_zero]
    apply hfg x.2
  · simp_rw [iteratedDeriv_succ']
    apply IH
    intro y hy
    apply Filter.EventuallyEq.deriv_eq
    rw [@Filter.eventuallyEq_iff_exists_mem]
    refine ⟨s, IsOpen.mem_nhds hs hy, hfg⟩

open scoped LSeries.notation in
theorem BadChar.abscissa {N : ℕ} [inst : NeZero N] (B : BadChar N) :
    LSeries.abscissaOfAbsConv ↗B.e < 2 := by
  have H : LSeries.abscissaOfAbsConv ↗B.e ≤ (3 / 2 : ℝ) := by
    convert LSeriesSummable.abscissaOfAbsConv_le (s := (3 / 2 : ℝ)) ?_
    exact B.e_summable (s := (3 / 2 : ℝ))
            (by simp only [ofReal_div, ofReal_ofNat, div_ofNat_re, re_ofNat]; norm_num)
  refine H.trans_lt ?_
  rw [show (2 : EReal) = (2 : ℝ) from rfl]
  norm_cast
  norm_num

/-- The goal: bad characters do not exist. -/
theorem BadChar.elim (B : BadChar N) : False := by
  have h1 := B.e_nonneg
  have h2 := B.F_neg_two
  have h3 := B.F_differentiable
  have h5 := derivs_from_coeffs B.e (fun n ↦ h1 n) 2 (BadChar.abscissa B)
  · have := Complex.at_zero_le_of_iteratedDeriv_alternating (f := fun s ↦ B.F (s + 2)) (z := -4)
      ?_ ?_
    · simp only [Left.neg_nonpos_iff, Nat.ofNat_nonneg, zero_add, true_implies] at this
      have h6 := BadChar.F_two_pos B
      have : 0 < B.F (-2) := by
        apply lt_of_lt_of_le h6
        norm_cast at *
      linarith
    · apply Differentiable.comp h3
      simp only [differentiable_id', differentiable_const, Differentiable.add]
    · intro n _
      have h55 := h5 n
      rw [iteratedDeriv_comp_const_add] at h55
      have := iteratedDeriv_eq_on_open n (f := fun s ↦ B.F (s + 2))
        (g := fun z ↦ LSeries (fun x ↦ ↑(B.e x)) (↑2 + z)) (s := {s | 1 < (s + 2).re}) ?_ ?_
          (x := ⟨(0 : ℂ), by simp only [add_re, re_ofNat, Set.mem_setOf_eq, zero_re, zero_add,
            Nat.one_lt_ofNat]⟩)
      · rw [this]
        apply h55
      · apply isOpen_lt
        exact continuous_const
        refine Continuous.comp' (Complex.continuous_re) (continuous_add_right 2)
      · intro x hx
        simp only
        rw [B.F_eq_LSeries (s := x + 2), add_comm]
        apply hx
