open import group
open import Data.Integer.Base using (ℤ; 0ℤ; -_; _⊖_)
open import Data.Nat.Base using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_ )
open import Level using (Level; _⊔_; suc)
open import Relation.Unary using (_⊆_; _∈_; Pred; ｛_｝)

module group.subgroup where 
open Group

record Subgroup {a l₁ l₂} (A : Set a) (_·_ : A → A → A)
  (_⁻¹ : A → A) (_≈_ : Rel A l₁) : (Set (Level.suc (a ⊔ l₁ ⊔ l₂))) where
  field
    parentSet : Pred A a
    parent : Group A _·_ _⁻¹ _≈_
    set : Pred A l₂
    subset : set ⊆ parentSet
    closedMultiplication : {x y : A} → (x ∈ set)
      → (y ∈ set) → (x · y) ∈ set
    closedInverse : (x : A) → (x ∈ set) → (x ⁻¹) ∈ set

trivial-identity : {a l m : Level} → (A : Set a) → {_·_ : A → A → A} →
  {_⁻¹ : A → A} → {_≈_ : Rel A l} → Group {a} {l} A _·_ _⁻¹ _≈_ →
  Subgroup A _·_ _⁻¹ _≈_
trivial-identity A g@(record { identity = identity ; id-law = id-law ; inverse-law = inverse-law }) =
  record
    { parentSet = λ x → A
    ; parent = record
      { identity = identity
      ; id-law = id-law
      ; inverse-law = inverse-law
      }
    ; set = ｛ identity ｝
    ; subset =  λ{ _≡_.refl → identity }
    ; closedMultiplication = {!helper!}
    ; closedInverse = λ{ x _≡_.refl → {!!} }
    }
  where
    helper :  {x y : A} → x ∈ ｛ identity ｝ → y ∈ ｛ identity ｝ → (x · y) ∈ ｛ identity ｝
--      helper

