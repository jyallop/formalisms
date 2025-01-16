open import Level

data ⊥ : Set where

¬_ : (A : Set) → Set
¬_ A = A → ⊥

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

contrapositive : {A : Set} → {B : Set} → (A → B) → ((¬ B) → (¬ A))
contrapositive f notb = λ x → notb (f x)

data _∨_  (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data _∧_ (A B : Set) : Set where
  and : A → B → A ∧ B

or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left x) l r = l x
or-elim (right x) l r = r x

and-elim-left : {A B : Set} → (A ∧ B) → A
and-elim-left (and a b) = a

and-elim-right : {A B : Set} → (A ∧ B) → B
and-elim-right (and a b) = b 

uncurry : {A B C : Set} → (A ∧ B → C) → (A → B → C)
uncurry f a b = f (and a b)

curry : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry f = λ{ (and a b) → f a b }

demorgan-∧ : {A B : Set} → (¬ A) ∧ (¬ B) → ¬ (A ∨ B)
demorgan-∧ (and a b) = λ x → or-elim x a b

demorgan-∨ : {A B : Set} → (¬ A) ∨ (¬ B) → ¬ (A ∧ B)
demorgan-∨ (left f) = λ{ (and a b) → f a }
demorgan-∨ (right f) = λ{ (and a b) → f b }

lemma-one : {A : Set} → ¬ (A ∧ (¬ A))
lemma-one = λ{ (and a nota) → nota a }

lemma-two : {A B : Set} → ¬ (A ∨ B) → (¬ A) ∧ (¬ B) 
lemma-two prop = and (λ a → prop (left a)) λ b → prop (right b)

harper-exercise : {A : Set} → ¬ (¬ (A ∨ (¬ A)))
harper-exercise {A} = λ prop → lemma-one (lemma-two prop)
