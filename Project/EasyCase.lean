import Project.EulerProducts.PNT
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Lemma 2: non-vanishing for `t ≠ 0` or `χ² ≠ 1`
-/

open Complex in
lemma continuous_cpow_natCast_neg (n : ℕ) [NeZero n] : Continuous fun s : ℂ ↦ (n : ℂ) ^ (-s) := by
  refine Continuous.cpow continuous_const continuous_neg fun _ ↦ ?_
  simp only [natCast_mem_slitPlane, ne_eq, (Nat.prime_of_mem_primeFactors hp).ne_zero,
    not_false_eq_true, NeZero.ne]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

open Complex BigOperators

open scoped LSeries.notation

section

open Filter Topology Homeomorph Asymptotics

namespace DirichletCharacter

noncomputable
abbrev LFunction_one (N : ℕ) [NeZero N] := (1 : DirichletCharacter ℂ N).LFunction

lemma LSeries_changeLevel (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rw [prod_eq_tprod_mulIndicator, ← dirichletLSeries_eulerProduct_tprod _ hs,
    ← dirichletLSeries_eulerProduct_tprod _ hs]
  -- not sure why the `show` is needed here, `tprod_subtype` doesn't bite otherwise
  show ∏' p : ↑{p : ℕ | p.Prime}, _ = (∏' p : ↑{p : ℕ | p.Prime}, _) * _
  rw [tprod_subtype (s := ↑{p : ℕ | p.Prime})
    (f := fun p ↦ (1 - (changeLevel hMN χ) p * p ^ (-s))⁻¹)]
  rw [tprod_subtype (s := ↑{p : ℕ | p.Prime}) (f := fun p ↦ (1 - χ p * p ^ (-s))⁻¹), ← tprod_mul]
  rotate_left -- deal with convergence goals first
  · rw [← multipliable_subtype_iff_mulIndicator]
    exact (dirichletLSeries_eulerProduct_hasProd χ hs).multipliable
  · rw [← multipliable_subtype_iff_mulIndicator]
    exact Multipliable.of_finite
  · congr 1 with p
    simp only [Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_primeFactors,
      ne_eq, mul_ite, ite_mul, one_mul, mul_one]
    by_cases h : p.Prime; swap
    · simp only [h, false_and, if_false]
    simp only [h, true_and, if_true]
    by_cases hp' : p ∣ N; swap
    · simp only [hp', false_and, ↓reduceIte, inv_inj, sub_right_inj, mul_eq_mul_right_iff,
        cpow_eq_zero_iff, Nat.cast_eq_zero, ne_eq, neg_eq_zero]
      have hq : IsUnit (p : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd h).mpr hp'
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hq.unit
      simp only [IsUnit.unit_spec] at this
      simp only [this, ZMod.cast_natCast hMN, true_or]
    · simp only [hp', NeZero.ne N, not_false_eq_true, and_self, ↓reduceIte]
      have : ¬IsUnit (p : ZMod N) := by rwa [ZMod.isUnit_prime_iff_not_dvd h, not_not]
      rw [MulChar.map_nonunit _ this, zero_mul, sub_zero, inv_one]
      refine (inv_mul_cancel₀ ?_).symm
      rw [sub_ne_zero, ne_comm]
      -- Remains to show `χ p * p ^ (-s) ≠ 1`. We show its norm is strictly `< 1`.
      apply_fun (‖·‖)
      simp only [norm_mul, norm_one]
      have ha : ‖χ p‖ ≤ 1 := χ.norm_le_one p
      have hb : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := norm_prime_cpow_le_one_half ⟨p, h⟩ hs
      exact ((mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_lt (by norm_num)).ne

lemma LFunction_changeLevel' {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) : LFunction (changeLevel hMN χ) s =
    LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) := by
    refine (isConnected_compl_singleton_of_one_lt_rank ?_ _).isPreconnected
    simp only [rank_real_complex, Nat.one_lt_ofNat]
  have hne : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (g := fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction ((changeLevel hMN) χ) s (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .finset_prod fun i hi ↦ ?_
    refine (differentiableAt_const _).sub ((differentiableAt_const _).mul ?_)
    apply differentiableAt_id.neg.const_cpow
    exact .inl (mod_cast (Nat.pos_of_mem_primeFactors hi).ne')
  · refine eventually_of_mem ?_  (fun t (ht : 1 < t.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : 1 < (2 : ℂ).re)
    · simpa only [LFunction_eq_LSeries _ ht] using LSeries_changeLevel M N hMN χ t ht

lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    (changeLevel hMN χ).LFunction s =
       χ.LFunction s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · simp only [ne_eq, not_true_eq_false, or_false] at h
    have hχ : changeLevel hMN χ ≠ 1 :=
      fun H ↦ h <| (changeLevel_eq_one_iff hMN).mp H
    have h₂ := (differentiable_LFunction (χ := changeLevel hMN χ) hχ).continuous
    have h₃ :
        Continuous fun s ↦ χ.LFunction s * ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) :=
      Continuous.mul (differentiable_LFunction h).continuous <|
        continuous_finset_prod _ fun p hp ↦ Continuous.sub continuous_const <|
        Continuous.mul continuous_const <|
          @continuous_cpow_natCast_neg p ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    have H s (hs : s ≠ 1) := LFunction_changeLevel' hMN χ hs
    revert s
    rw [← funext_iff]
    exact Continuous.ext_on (dense_compl_singleton 1) h₂ h₃ H
  · exact LFunction_changeLevel' hMN χ h

lemma LFunction_one_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunction_one N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunction_one, ← changeLevel_one N.one_dvd, mul_comm]
  convert LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

lemma LFunction_one_residue_one :
  Filter.Tendsto (fun s ↦ (s - 1) * LFunction_one N s) (nhdsWithin 1 {1}ᶜ)
    (nhds <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  -- need to use that `s ≠ 1`
  have H : (fun s ↦ (s - 1) * LFunction_one N s) =ᶠ[nhdsWithin 1 {1}ᶜ]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunction_one_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  convert Filter.Tendsto.mul (f := fun s ↦ ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s)))
    ?_ riemannZeta_residue_one
  apply tendsto_nhdsWithin_of_tendsto_nhds
  refine Continuous.tendsto ?_ 1
  exact continuous_finset_prod _ fun p hp ↦ Continuous.sub continuous_const <|
    @continuous_cpow_natCast_neg p ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩

end DirichletCharacter

open DirichletCharacter

/-- A variant of `norm_dirichlet_product_ge_one` in terms of the L functions. -/
lemma norm_dirichletLFunction_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖LFunction_one N (1 + x) ^ 3 * χ.LFunction (1 + x + I * y) ^ 4 *
      (χ ^ 2).LFunction (1 + x + 2 * I * y)‖ ≥ 1 := by
  convert norm_dirichlet_product_ge_one χ hx y using 3
  · congr 2
    · refine DirichletCharacter.LFunction_eq_LSeries 1 ?_
      simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx]
    · refine χ.LFunction_eq_LSeries ?_
      simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, lt_add_iff_pos_right, hx]
  · refine (χ ^ 2).LFunction_eq_LSeries ?_
    simp only [add_re, one_re, ofReal_re, mul_re, re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one,
      sub_self, zero_mul, mul_im, add_zero, ofReal_im, lt_add_iff_pos_right, hx]

lemma dirichletLFunction_one_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ LFunction_one N (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ LFunction_one N (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * LFunction_one N (1 + w)) (𝓝[≠] 0)
               (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
      convert Tendsto.comp (f := fun w ↦ 1 + w) (LFunction_one_residue_one (N := N)) ?_ using 1
      · ext w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> simp
    exact ((isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhds_right'_le_nhds_ne 0

lemma dirichletLFunction_isBigO_of_ne_one_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    (fun x : ℝ ↦ χ.LFunction (1 + x + I * y)) =O[𝓝[>] 0] (fun _ ↦ (1 : ℂ)) := by
  refine Asymptotics.IsBigO.mono ?_ nhdsWithin_le_nhds
  have hy' : 1 + I * y ≠ 1 ∨ χ ≠ 1:= by
    simp only [ne_eq, add_right_eq_self, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or, hy]
  convert isBigO_comp_ofReal
    (χ.differentiableAt_LFunction _ hy').continuousAt.isBigO using 3 with x
  ring

lemma dirichletLFunction_isBigO_near_root_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1)
    (h : χ.LFunction (1 + I * y) = 0) :
    (fun x : ℝ ↦ χ.LFunction (1 + x + I * y)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  have hy' : 1 + I * y ≠ 1 ∨ χ ≠ 1:= by simp [hy]
  conv => enter [2, x]; rw [add_comm 1, add_assoc]
  refine (isBigO_comp_ofReal <| DifferentiableAt.isBigO_of_eq_zero ?_ h).mono
    nhdsWithin_le_nhds
  exact χ.differentiableAt_LFunction (1 + I * ↑y) hy'

/-- The L function of a Dirichlet character `χ` does not vanish at `1 + I*t` if `t ≠ 0`
or `χ^2 ≠ 1`. -/
theorem mainTheorem_general {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    χ.LFunction (1 + I * t) ≠ 0 := by
  intro Hz
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      (fun x ↦ LFunction_one N (1 + x) ^ 3 * χ.LFunction (1 + x + I * t) ^ 4 *
                   (χ ^ 2).LFunction (1 + x + 2 * I * t)) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun _ hx ↦ (norm_one (α := ℝ)).symm ▸ (norm_dirichletLFunction_product_ge_one hx t).le
  have hz₁ : t ≠ 0 ∨ χ ≠ 1 := by
    rcases h with h | h
    · refine .inr ?_
      rintro rfl
      simp only [one_pow, ne_eq, not_true_eq_false] at h
    · exact .inl h
  have hz₂ : 2 * t ≠ 0 ∨ χ ^ 2 ≠ 1 := by
    rcases h with h | h
    · exact .inr h
    · exact .inl <| mul_ne_zero two_ne_zero h
  have H := ((dirichletLFunction_one_isBigO_near_one_horizontal (N := N)).pow 3).mul
    ((dirichletLFunction_isBigO_near_root_horizontal hz₁ Hz).pow 4)|>.mul <|
    dirichletLFunction_isBigO_of_ne_one_horizontal hz₂
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · field_simp [h]
      ring
  conv at H => enter [3, x]; rw [help]
  conv at H =>
    enter [2, x]; rw [show 1 + x + I * ↑(2 * t) = 1 + x + 2 * I * t by simp; ring]
  replace H := (H₀.trans H).norm_right
  simp only [norm_eq_abs, abs_ofReal] at H
  refine isLittleO_irrefl ?_ <| H.of_abs_right.trans_isLittleO <|
    isLittleO_id_one.mono nhdsWithin_le_nhds
  simp only [ne_eq, one_ne_zero, not_false_eq_true, frequently_true_iff_neBot]
  exact mem_closure_iff_nhdsWithin_neBot.mp <| closure_Ioi (0 : ℝ) ▸ Set.left_mem_Ici

end
