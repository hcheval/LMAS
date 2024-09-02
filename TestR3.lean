import Mathlib 

macro "use" e:term : tactic => `(tactic| refine Exists.intro $e ?_)

set_option autoImplicit false

/-
  Fill the `sorry`s below.
  You may **not** use the `simp` tactic or theorems from the standard library for
    the proofs in Exercises 2 ... 5.
  Each exercise is worth 1 point.

  You can use a local Lean installation, or the web editor at: https://live.lean-lang.org/

-/

/-
  **Exercise 1**: Define the `prodN : Nat → Nat → Nat` function
    such that, for all `a b : Nat`, `prodN a b` computes the product of the first
    `b` natural numbers starting from `a`.
    The sum of 0 numbers is defined to be 1.
  The definition must be given by recursion.
-/
def prodN (a : Nat) (b : Nat) : Nat := sorry

section
  variable (p q : Prop)

/-
  **Exercise 2**: Prove the following theorem.
-/
  theorem ex2 : (p → q) ∧ ¬q → ¬p  := sorry  

end


section

  variable {α : Type} (p : α → Prop) 

/-
  **Exercise 3**: Prove the following theorem.
-/
  theorem ex3 : ((∀ x, p x) → (¬∃ x, ¬ p x)) ∨ ((¬∃ x, ¬ p x) → (∀ x, p x)) := sorry 



end


section
/-
  **Exercise 4**: Prove the following theorem.
-/
  theorem ex4 : ¬(∀ p : Prop, p) := sorry

end


section
  opaque Box : Prop → Prop

  prefix:max "□" => Box

  set_option hygiene false in prefix:100 "⊢K" => KProvable
  inductive KProvable : Prop → Prop where
  | tautology {p : Prop} : p → ⊢K p    -- this rule is oversimplified for the puprose of this lab; we will only used for propositional tautologies
  | modusPonens {p q : Prop} : ⊢K p → ⊢K (p → q) → ⊢K q
  | K {p q : Prop} : ⊢K (□(p → q) → □p → □q)
  | necessitation {p : Prop} : ⊢K p → ⊢K □p

  open KProvable

  variable (p q : Prop)

/-
  **Exercise 5**: Prove the following theorem.
-/
  theorem ex5 : ⊢K (□□(p ∧ q) → □□(q ∧ p)) := sorry 
end
