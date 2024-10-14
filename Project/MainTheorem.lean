import Project.PropertiesF

open Complex

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

theorem mainTheorem_quadratic (hχ : χ ^ 2 = 1) :
    χ.LFunction 1 ≠ 0 := by
  sorry

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
