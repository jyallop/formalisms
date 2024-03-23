open import Data.Product using (∃; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Identity {A : Set} (x : A) (· : A → A → A) : Set where
  identity : ∃[ x ] (∀ y → (x · y ≡ y) × (y · x ≡ y)) → Identity x ·

record Monoid (A : Set) (op : A → A → A) : Set where
  field
    Obj : A
    · : A → A → A
    identity : Identity Obj 
    
