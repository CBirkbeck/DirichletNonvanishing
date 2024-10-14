import Mathlib

-- The object we're trying to show doesn't exist.
structure BadChar (N : ℕ) [NeZero N] where
  χ : DirichletCharacter ℝ N
  hχ : DirichletCharacter.LFunction (χ.ringHomComp Complex.ofRealHom) 1 = 0

variable {N : ℕ} [NeZero N]

noncomputable section

def BadChar.F (B : BadChar N) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction (B.χ.ringHomComp Complex.ofRealHom) s

lemma BadChar.F_differentiableAt_of_ne (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (B.F) s := by
  sorry
