open import lambda-calculus
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

record Λ⁰ : Set where
  field
    term : Λ
    closed : Empty FV⟨ term ⟩

K : Λ
K = ƛ ("x", 1) ⇒ (ƛ ("y", 1) ⇒ ` ("x", 1))

S : Λ
S = ƛ ("x", 1) ⇒ (ƛ ("y", 1) ⇒ (ƛ ("z", 1) ⇒ (` ("x", 1) · ` ("z", 1) · (` ("y", 1) · ` ("z", 1))))) 

record zero : Set where

postulate equation : S ＝ K

record _♯_ (m n : Λ) : Set₁ where
  field
    inconsistent : Σ (m ＝ n) (λ axiom → _)

