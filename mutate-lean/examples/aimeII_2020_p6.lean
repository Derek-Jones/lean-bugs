import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Define a sequence recursively by $t_1 = 20$, $t_2 = 21$, and$t_n = \frac{5t_{n-1}+1}{25t_{n-2}}$for all $n \ge 3$. Then $t_{2020}$ can be expressed as $\frac{p}{q}$, where $p$ and $q$ are relatively prime positive integers. Find $p+q$. Show that it is 626.-/
theorem aimeII_2020_p6 (t : ℕ → ℚ) (h₀ : t 1 = 20) (h₁ : t 2 = 21)
  (h₂ : ∀ n ≥ 3, t n = (5 * t (n - 1) + 1) / (25 * t (n - 2))) :
  ↑(t 2020).den + (t 2020).num = 626 := by
  have h3 : t 3 = (5 * t 2 + 1) / (25 * t 1) := by
    simp [h₂, h₀, h₁]
    -- Simplify the expression for t₃ using the given recursive formula and initial conditions.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula again.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
    -- Normalize the numerical expressions again to ensure correctness.
    <;> simp_all [h₂]
    -- Simplify all expressions using the recursive formula.
    <;> norm_num
  
  have h4 : t 4 = (5 * t 3 + 1) / (25 * t 2) := by
    have h4 : t 4 = (5 * t 3 + 1) / (25 * t 2) := by
      apply h₂
      all_goals norm_num
    all_goals assumption
  
  have h5 : t 5 = (5 * t 4 + 1) / (25 * t 3) := by
    simpa [h₀, h₁, h3, h4] using h₂ 5 (by norm_num)
  
  have h6 : t 6 = (5 * t 5 + 1) / (25 * t 4) := by
    simpa [h₀, h₁, h₂, h3, h4, h5] using h₂ 6 (by decide)
  
  have h7 : t 7 = (5 * t 6 + 1) / (25 * t 5) := by
    simp_all [h₂]
    -- Simplify all hypotheses using the recursive formula to express t 7 in terms of t 6 and t 5.
    <;> norm_num
    -- Normalize the numerical values to ensure consistency with the given initial conditions.
    <;> linarith
    -- Use linear arithmetic to verify the consistency of the computed values.
    <;> rfl
  
  have h8 : t 8 = (5 * t 7 + 1) / (25 * t 6) := by
    -- We will use the given initial conditions and the recurrence relation to find t_8.
    norm_num [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *
    -- Simplify the expressions using the initial conditions and the recurrence relation.
    <;> simp_all [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    -- Use linear arithmetic to verify the final result.
    <;> linarith
  
  have h9 : t 9 = (5 * t 8 + 1) / (25 * t 7) := by
    norm_num [h₂, h3, h4, h5, h6, h7, h8] at *
    <;> simp_all [h₂, h3, h4, h5, h6, h7, h8] <;> norm_num
    <;> ring
    <;> linarith
  
  have h10 : t 10 = (5 * t 9 + 1) / (25 * t 8) := by
    -- Use the recursive definition of t_n to compute t_10
    norm_num [h₂, h₀, h₁, h3, h4, h5, h6, h7, h8, h9]
    <;> field_simp
    <;> ring
    <;> norm_num
    <;> linarith
  
  have cycle : t 6 = t 1 ∧ t 7 = t 2 ∧ t 8 = t 3 ∧ t 9 = t 4 ∧ t 10 = t 5 := by
    refine' ⟨_, _, _, _, _⟩
    <;> norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at *
    <;> linarith
    <;> norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at *
    <;> linarith
    <;> norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at *
    <;> linarith
    <;> norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at *
    <;> linarith
    <;> norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at *
    <;> linarith
  
  have mod : 2020 % 5 = 0 := by
    have h₁₁ := cycle.1
    have h₁₂ := cycle.2.1
    have h₁₃ := cycle.2.2.1
    have h₁₄ := cycle.2.2.2.1
    have h₁₅ := cycle.2.2.2.2
    norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅] at *
    <;> ring_nf at *
    <;> linarith
  
  have t2020 : t 2020 = t 5 := by
    have step1 : t 3 = (5 * 21 + 1) / (25 * 20) := by
      have h₃ := h₂ 3
      have h₄ := h₂ 4
      have h₅ := h₂ 5
      have h₆ := h₂ 6
      have h₇ := h₂ 7
      have h₈ := h₂ 8
      have h₉ := h₂ 9
      have h₁₀ := h₂ 10
      norm_num [h₀, h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, cycle, mod] at *
      <;> linarith
    
    have step2 : t 4 = (5 * t 3 + 1) / (25 * 21) := by
      have h₁₁ := cycle.1
      have h₁₂ := cycle.2.1
      have h₁₃ := cycle.2.2.1
      have h₁₄ := cycle.2.2.2.1
      have h₁₅ := cycle.2.2.2.2
      have h₁₆ := h₂ 3 (by norm_num)
      have h₁₇ := h₂ 4 (by norm_num)
      have h₁₈ := h₂ 5 (by norm_num)
      have h₁₉ := h₂ 6 (by norm_num)
      have h₂₀ := h₂ 7 (by norm_num)
      have h₂₁ := h₂ 8 (by norm_num)
      have h₂₂ := h₂ 9 (by norm_num)
      have h₂₃ := h₂ 10 (by norm_num)
      norm_num [h₀, h₁, h3, h4, h5, h6, h7, h8, h9, h10, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁, h₂₂, h₂₃] at *
      <;> linarith
    
    have step3 : t 5 = (5 * t 4 + 1) / (25 * t 3) := by
      norm_num [h₀, h₁, h3, h4, h5, h6, h7, h8, h9, h10, cycle, mod, step1, step2] at *
      <;> linarith
      <;> norm_num
      <;> linarith
    
    have step4 : t 6 = t 1 := by
      have h₁₁ := h₂ 3 (by norm_num)
      have h₁₂ := h₂ 4 (by norm_num)
      have h₁₃ := h₂ 5 (by norm_num)
      have h₁₄ := h₂ 6 (by norm_num)
      have h₁₅ := h₂ 7 (by norm_num)
      have h₁₆ := h₂ 8 (by norm_num)
      have h₁₇ := h₂ 9 (by norm_num)
      have h₁₈ := h₂ 10 (by norm_num)
      norm_num [h₀, h₁, h3, h4, h5, h6, h7, h8, h9, h10, cycle] at *
      <;> linarith
    
    have step5 : t 7 = t 2 := by
      simp [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10, cycle, mod, step1, step2, step3, step4]
      <;> norm_num
      <;> linarith
    
    have step6 : t 8 = t 3 := by
      simp [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10, cycle, mod, step1, step2, step3, step4, step5] at *
      <;> linarith
    
    have step7 : t 9 = t 4 := by
      simp [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at step1 step2 step3 cycle ⊢
      <;> linarith
    
    have step8 : t 10 = t 5 := by
      have h₀' := step4
      have h₁' := step5
      have h₂' := step6
      have h₃' := step7
      have h₄ := cycle.1
      have h₅ := cycle.2.1
      have h₆ := cycle.2.2.1
      have h₇ := cycle.2.2.2.1
      have h₈ := cycle.2.2.2.2
      have h₉ := mod
      have h₁₀ := step1
      have h₁₁ := step2
      have h₁₂ := step3
      norm_num [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10] at h₀' h₁' h₂' h₃' h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ ⊢
      <;> linarith
    
    have step9 : ∀ k, t (5 * k + 1) = t 1 ∧ t (5 * k + 2) = t 2 ∧ t (5 * k + 3) = t 3 ∧ t (5 * k + 4) = t 4 ∧ t (5 * k + 5) = t 5 := by
      -- Introduce a counter k and apply the cycle property to the terms t (5 * k + 1) to t (5 * k + 5)
      intro k
      -- Use the cycle property to show that the terms repeat in a certain way
      have h11 := cycle.1
      have h12 := cycle.2.1
      have h13 := cycle.2.2.1
      have h14 := cycle.2.2.2.1
      have h15 := cycle.2.2.2.2
      -- Use the repeated application of the recurrence relation to show that the terms follow the cycle pattern
      simp at h11 h12 h13 h14 h15
      -- Use the induction principle to prove that the terms follow the cycle pattern for all k
      induction k <;> simp [*, Nat.mul_succ] at *
      <;> norm_num
      <;> linarith
    
    have step10 : 2020 = 5 * 404 := by
      have h11 := cycle.1
      have h12 := cycle.2.1
      have h13 := cycle.2.2.1
      have h14 := cycle.2.2.2.1
      have h15 := cycle.2.2.2.2
      have h16 := step9 0
      have h17 := h16.1
      have h18 := h16.2.1
      have h19 := h16.2.2.1
      have h20 := h16.2.2.2.1
      have h21 := h16.2.2.2.2
      norm_num [h₀, h₁, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h17, h18, h19, h20, h21] at *
      <;> linarith
    
    have step11 : t 2020 = t (5 * 404) := by
      norm_num [h₀, h₁, h3, h4, h5, h6, h7, h8, h9, h10, cycle, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10] at *
      <;> simp_all
      <;> norm_num
      <;> linarith
    
    have step12 : t (5 * 404) = t 5 := by
      have h₁₂ := step9 404
      have h₁₃ := step9 403
      have h₁₄ := step9 402
      have h₁₅ := step9 401
      have h₁₆ := step9 400
      norm_num [h₁₂, h₁₃, h₁₄, h₁₅, h₁₆]
      <;> simp_all
      <;> ring
      <;> linarith
    have final : t 2020 = t 5 := by
      simp only [step12, step11, h6, h7, h8, h9, h10, cycle, h5, h4, h3, h₂, h₀, h₁] at *
      <;> norm_num
      <;> linarith
    
    -- Since the sequence repeats every 5 terms, we can directly use the fact that t_2020 = t_5.
    simpa [final] using final
  
  have simplified : t 5 = 5353 / 27825 := by
    norm_num [h₀, h₁, h3, h4, h5, h6, h7, h8, h9, h10, cycle, mod, t2020] at *
    <;> linarith
    <;> norm_num
    <;> linarith
  
  have sum : ↑(t 2020).den + (t 2020).num = 626 := by
    norm_num [cycle, mod, t2020, simplified] at *
    <;> norm_cast
    <;> norm_num
    <;> norm_cast
    <;> norm_num
    <;> norm_cast
    <;> norm_num
    <;> norm_cast
    <;> norm_num
    <;> norm_cast
  norm_num [cycle, simplified, sum]
  <;> simp_all [h₀, h₁, h₂, h3, h4, h5, h6, h7, h8, h9, h10, t2020, simplified, sum]
  <;> norm_cast
  <;> rfl

