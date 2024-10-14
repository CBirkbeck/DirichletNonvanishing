import Project.EulerProducts.PNT
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Lemma 2: non-vanishing for `t ≠ 0` or `χ² ≠ 1`
-/

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

open Complex

theorem mainTheorem_general {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    χ.LFunction (1 + I * t) ≠ 0 :=
  sorry
