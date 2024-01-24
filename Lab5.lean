
/-**Modal logic**-/

/-
  Modal logic is not a native part of Lean.
  As such, we will have to define it ourselves, beginning with the modal operators.
-/

opaque Box : Prop → Prop

prefix:max "□" => Box

/- **Exercise 1**: Give the standard definition of diamond in terms of box. -/
def Diamond (p : Prop) : Prop := ¬□¬p

prefix:max "⋄" => Diamond

/-
  We define provability in the `K` logic, by adding all proof rules in an inductive type.
  You can ignore the details, just focus on the correspondence between these rules
  and their "pen and paper" formulation
-/
set_option hygiene false in prefix:100 "⊢K" => KProvable
inductive KProvable : Prop → Prop where
| tautology {p : Prop} : p → ⊢K p    -- this rule is oversimplified for the puprose of this lab; we will only used for propositional tautologies
| modusPonens {p q : Prop} : ⊢K p → ⊢K (p → q) → ⊢K q
| K {p q : Prop} : ⊢K (□(p → q) → □p → □q)
| necessitation {p : Prop} : ⊢K p → ⊢K □p

open KProvable

variable {p q : Prop}

/- The first proof is just a propositional theorem, which is "imported" in our system via `tautology` -/
example : ⊢K (□p ∨ ¬□p) := by
  have l₁ : □p ∨ ¬□p := Classical.em _
  exact tautology l₁

/- The same as before, plus an additional use of `necessitation` -/
example : ⊢K □(p → p) := by
  have l₁ : p → p := fun hp => hp
  have l₂ : ⊢K (p → p) := tautology l₁
  exact necessitation l₂

/- The translation of a standard proof you can find in the lecture notes -/
theorem example1 : ⊢K (p → q) → ⊢K (□p → □q) := by
  intros h
  have l₁ : ⊢K □(p → q) := necessitation h
  have l₂ : ⊢K (□(p → q) → □p → □q) := K
  exact modusPonens l₁ l₂

/- You can use propositional proofs from previous labs, when needed -/

/- **Exercise 2** -/
example : ⊢K (□p → □¬¬p) := by
  have l₁ : p → ¬¬p := fun hp hnp => hnp hp
  have l₂ : ⊢K (p → ¬¬p) := tautology l₁
  have l₃ : ⊢K □(p → ¬¬p) := necessitation l₂
  have l₃ : ⊢K (□p → □¬¬p) := modusPonens l₃ K
  exact l₃

/- **Exercise 3**-/
theorem ex3 : ⊢K (□p → □(q → p)) := by
  have l₁ : p → q → p := fun hp hq => hp
  have l₂ : ⊢K (p → q → p) := tautology l₁
  have l₃ : ⊢K □(p → q → p) := necessitation l₂
  have l₃ : ⊢K (□p → □(q → p)) := modusPonens l₃ K
  exact l₃

/- **Exercise 4** -/
example : ⊢K □p → ⊢K □(q → p) := by
  intros l₁
  exact modusPonens l₁ ex3

/- **Exercise 6** -/
theorem ex6 : ⊢K (□(p ∧ q) → □p ∧ □q) := by
  have l₁ : p ∧ q → p := fun h => And.left h
  have l₂ : ⊢K (p ∧ q → p) := tautology l₁
  have l₃ : ⊢K (□(p ∧ q) → □p) := example1 l₂
  have l₄ : p ∧ q → q := fun h => And.right h
  have l₅ : ⊢K (p ∧ q → q) := tautology l₄
  have l₆ : ⊢K (□(p ∧ q) → □q) := example1 l₅
  have l₇ : ∀ {r₁ r₂ r₃ : Prop}, ⊢K ((r₁ → r₂) → (r₁ → r₃) → (r₁ → r₂ ∧ r₃)) :=
    tautology (fun h h' h'' => And.intro (h h'') (h' h''))
  have l₈ := modusPonens l₆ (modusPonens l₃ l₇)
  exact l₈


/- **Exercise 5** -/
example : ⊢K (p → q) → ⊢K (⋄p → ⋄q) := by
  intros l₁
  have l₂ : ∀ {r₁ r₂ : Prop}, ⊢K ((r₁ → r₂) → (¬r₂ → ¬r₁)) :=
    tautology (fun h h' h'' => h' (h h''))
  have l₃ : ⊢K (¬q → ¬p) := modusPonens l₁ l₂
  have l₄ : ⊢K (□¬q → □¬p) := example1 l₃
  have l₅ : ⊢K ((□¬q → □¬p) → (¬□¬p → ¬□¬q)) := l₂
  have l₅ : ⊢K (¬□¬p → ¬□¬q) := modusPonens l₄ l₅
  exact l₅


/- **Exercise 7** -/
theorem ex7 : ⊢K (□p ∧ □q → □(p ∧ q)) := by
  have l₁ : ⊢K (p → q → (p ∧ q)) := tautology (And.intro)
  have l₂ : ⊢K (□p → □(q → (p ∧ q))) := example1 l₁
  have l₃ : ⊢K (□(q → p ∧ q) → □q → □(p ∧ q)) := K
  have l₄ : ∀ {r₁ r₂ r₃ : Prop}, ⊢K ((r₁ → r₂) → (r₂ → r₃) → (r₁ → r₃)) :=
    tautology (fun h h' h'' => h' (h h''))
  have l₅ : ⊢K (□p → (□q → □(p ∧ q))) := modusPonens l₃ (modusPonens l₂ l₄)
  have l₆ : ∀ {r₁ r₂ r₃ : Prop}, ⊢K ((r₁ → r₂ → r₃) → r₁ ∧ r₂ → r₃) :=
    tautology (fun h h' => h h'.left h'.right)
  exact modusPonens l₅ l₆

