import Project.EulerProducts.PNT
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Lemma 2: non-vanishing for `t ≠ 0` or `χ² ≠ 1`
-/

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

open Complex

open scoped LSeries.notation

section

noncomputable
abbrev LFunction_one (N : ℕ) [NeZero N] := (1 : DirichletCharacter ℂ N).LFunction

open Filter Topology Homeomorph Asymptotics

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
    have H : Tendsto (fun w ↦ w * LFunction_one N (1 + w)) (𝓝[≠] 0) (𝓝 1) := by
      sorry
      -- convert Tendsto.comp (f := fun w ↦ 1 + w) riemannZeta_residue_one ?_ using 1
      -- · ext w
      --   simp only [Function.comp_apply, add_sub_cancel_left]
      -- · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
      --   convert map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> simp
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
