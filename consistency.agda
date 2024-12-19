open import lambda-calculus
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

record Λ⁰ : Set where
  field
    term : Λ
    closed : Empty FV⟨ term ⟩

I : Λ
I = ƛ ("x", 1) ⇒ ` ("x", 1)

K : Λ
K = ƛ ("x", 1) ⇒ (ƛ ("y", 1) ⇒ ` ("x", 1))

S : Λ
S = ƛ ("x", 1) ⇒ (ƛ ("y", 1) ⇒ (ƛ ("z", 1) ⇒ (` ("x", 1) · ` ("z", 1) · (` ("y", 1) · ` ("z", 1))))) 

record _♯_ (m n : Λ) : Set₁ where
  field
    inconsistent : m ＝ n → ((A B : Λ) → A ＝ B)

I♯K : I ♯ K
I♯K = record { inconsistent = λ x A B → {!!} }
