def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := 
  sorry

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := 
  λ f a b, f (a × b)

def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := 
  λ f x, f (fst x) (snd x)

def hellop (x : ℕ) : Prop := 
  x + 0 
