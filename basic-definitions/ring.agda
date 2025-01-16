open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Setoid; IsEquivalence; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_ )
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_)

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

record Field {n l : Level} (A : Set n) (_·_ : A → A → A) (_+_ : A → A → A) (_≈_ : Rel A l) : Set (n ⊔ l) where
  field
    identity : A
    id-law : (x : A) → (x · identity) ≈ x
    inverse-law : (x : A) → ∃[ y ] (((x · y) ≈ identity) × ((y · x) ≈ identity))
    
