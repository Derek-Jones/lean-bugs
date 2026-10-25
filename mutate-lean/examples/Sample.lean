/-! Sample proofs for the mutation tool (core Lean only). -/

namespace Sample

theorem add_comm' (a b : Nat) : a + b = b + a := by
  omega

-- a few tactic steps, so there is something to mutate
theorem two_steps (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c + 1 := by
  have h₃ : a ≤ c := Nat.le_trans h₁ h₂
  have h₄ : c ≤ c + 1 := Nat.le_succ c
  exact Nat.le_trans h₃ h₄

theorem list_len (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.length_cons]
                    omega

theorem and_swap (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  constructor
  · exact hq
  · exact hp

example : 2 + 2 = 4 := by decide

end Sample
