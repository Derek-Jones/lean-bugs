/-- A sequence with period 3: if `t (n + 3) = t n` and `t 0 = 7`, then `t 2019 = 7`.
    Core Lean only (no Mathlib), in the style of the AIME proof. -/
theorem core_cycle (t : Nat → Nat) (h₀ : t 0 = 7) (h₁ : t 1 = 4) (h₂ : t 2 = 9)
    (hp : ∀ n, t (n + 3) = t n) : t 2019 + t 2020 = 11 := by
  have step : ∀ k, t (3 * k) = t 0 ∧ t (3 * k + 1) = t 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : 3 * (k + 1) = 3 * k + 3 := by omega
      have e2 : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by omega
      constructor
      · rw [e1, hp]
        exact ih.1
      · rw [e2, hp]
        exact ih.2
  have h2019 : 2019 = 3 * 673 := by decide
  have h2020 : 2020 = 3 * 673 + 1 := by decide
  have a : t 2019 = 7 := by
    rw [h2019, (step 673).1, h₀]
  have b : t 2020 = 4 := by
    rw [h2020, (step 673).2, h₁]
  rw [a, b]

theorem small_facts (a b : Nat) (h : a < b) : a + 1 ≤ b ∧ a * 2 < b * 2 + 1 := by
  constructor
  · omega
  · have hb : a * 2 < b * 2 := by omega
    omega
