import Project.PropertiesF
import Mathlib.NumberTheory.MulChar.Lemmas

open Complex

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem mainTheorem_quadratic (hχ : χ ^ 2 = 1) :
    χ.LFunction 1 ≠ 0 := by
  intro hL
  -- tedious step: show that `χ` comes from a real-valued char
  obtain ⟨ξ, rfl⟩ :
      ∃ ξ : DirichletCharacter ℝ N, χ = ξ.ringHomComp ofRealHom := by
    have (x : ZMod N) : (χ x).im = 0 := by
      by_cases hx : IsUnit x
      · have hx' : (χ x) ^ 2 = 1 := by
          rw [← χ.pow_apply' two_ne_zero, hχ, MulChar.one_apply  hx]
        rw [sq_eq_one_iff] at hx'
        rcases hx' with h | h <;>
        · simp only [h, neg_im, one_im, neg_zero]
      · rw [χ.map_nonunit hx, zero_im]
    let ξ : DirichletCharacter ℝ N :=
    { toFun := fun x ↦ (χ x).re,
      map_one' := by simp only [map_one, one_re],
      map_mul' := by
        intro x y
        simp only [map_mul, mul_re, sub_eq_self, mul_eq_zero, this, true_or]
      map_nonunit' := by
        intro u hu
        simp only [χ.map_nonunit hu, zero_re] }
    use ξ
    ext a
    simp only [MulChar.ringHomComp_apply, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      ofRealHom_eq_coe, ξ]
    conv_lhs => rw [← re_add_im (χ a), this, ofReal_zero, zero_mul, add_zero]
  let B : BadChar N := {χ₀ := ξ, hχ := hL}
  exact B.elim

theorem mainTheorem_general {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    χ.LFunction (1 + I * t) ≠ 0 :=
  sorry

variable (χ) in
theorem ourMainTheorem {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) :
    χ.LFunction (1 + I * t) ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ t = 0
  · rw [h.2, ofReal_zero, mul_zero, add_zero]
    exact mainTheorem_quadratic h.1
  · rw [not_and_or] at h
    exact mainTheorem_general h
