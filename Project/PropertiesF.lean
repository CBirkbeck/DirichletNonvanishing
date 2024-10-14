import Mathlib.NumberTheory.LSeries.DirichletContinuation

-- The object we're trying to show doesn't exist.
structure BadChar (N : ℕ) [NeZero N] where
  χ₀ : DirichletCharacter ℝ N
  χ : DirichletCharacter ℂ N := χ₀.ringHomComp Complex.ofRealHom
  hχ : χ.LFunction 1 = 0

variable {N : ℕ} [NeZero N]

noncomputable section

lemma BadChar.χ_ne (B : BadChar N) : B.χ ≠ 1 := by
  sorry

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

/-- The goal: bad characters do not exist. -/
theorem BadChar.elim (B : BadChar N) : False :=
  sorry
