open import Level using (Level; _⊔_; suc)
open import Data.String using (String; _==_; _≟_)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- This definition comes from the book Higher Order Computability by John Longley
record Model {n : Level} (T : Set n) : Set (suc n) where
  field
    datatypes : T → Set n
    ops : (σ τ : T) → Set n

    -- properties/laws
    id : ∀{τ} → ops τ τ
    _·_ : ∀{σ τ ρ} → ops ρ σ → ops σ τ → ops ρ τ

data Expr : Set where
data Value : Set where

-- is defined
_↓ : Expr → Set

-- is undefined
_↑ : Expr → Set

eval : Expr → Value

_＝_ : (x y : Expr) → (x ↓) × (y ↓) × ((eval x) ≡ (eval y))


