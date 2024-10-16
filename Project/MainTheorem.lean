import Project.PropertiesF
import Mathlib.NumberTheory.MulChar.Lemmas
import Project.EasyCase

open Complex

variable {N : ℕ} [NeZero N]

/-- If `χ` is a nontrivial quadratic Dirichlet character, then `L(χ, 1) ≠ 0`. -/
theorem mainTheorem_quadratic {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (χ_ne : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 := by
  intro hL
  let B : BadChar N := {χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne}
  exact B.elim

/-- If `χ` is a Dirichlet character, then `L(χ, 1 + I*t)` does not vanish for `t ∈ ℝ`
except when `χ` is trivial and `t = 0` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem ourMainTheorem (χ : DirichletCharacter ℂ N) (t : ℝ) (hχt : χ ≠ 1 ∨ t ≠ 0) :
    χ.LFunction (1 + I * t) ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ t = 0
  · simp only [ne_eq, h.2, not_true_eq_false, or_false] at hχt
    rw [h.2, ofReal_zero, mul_zero, add_zero]
    exact mainTheorem_quadratic h.1 hχt
  · exact mainTheorem_general <| not_and_or.mp h
