open import Axiom.Extensionality.Propositional
open import Data.Integer.Base using (ℤ; 0ℤ; -_; _⊖_)
open import Data.Nat.Base using (zero)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Integer.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_ )
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_)
open import Level using (Level; _⊔_; suc)
open import Algebra.Definitions using (LeftCongruent; RightCongruent; Congruent₂; Congruent₁)
open import Data.Nat.Base using (ℕ; suc; zero; _+_)

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

record Group' {n l : Level} (A : Set n) (_·_ : A → A → A)
  (_⁻¹ : A → A) (_≈_ : Rel A l) : Set (n ⊔ l) where
  field
    identity : A
    id-law : (x : A) → (x · identity) ≈ x
    inverse-law : (x : A) → (((x · (x ⁻¹)) ≈ identity) × (((x ⁻¹) · x) ≈ identity))

record IsGroup {c} {ℓ} (Obj : Set c) (_≈_ : Rel Obj ℓ) (_·_ : Op₂ Obj) (ϵ : Obj) (_⁻¹ : Op₁ Obj) : Set (Level.suc (c ⊔ ℓ)) where
  field
    equivalence : IsEquivalence _≈_
    identity    : (x : Obj) → ((x · ϵ) ≈ x) × ((ϵ · x) ≈ x)
    inverse     : (x : Obj) → (((x ⁻¹) · x) ≈ ϵ) × ((x · (x ⁻¹)) ≈ ϵ)
    associative : (x y z : Obj) → ((x · y) · z) ≈ (x · (y · z))
    ⁻¹-cong    : Congruent₁ _≈_ _⁻¹
    ·-cong      : Congruent₂ _≈_ _·_

  setoid : Setoid c ℓ
  setoid = record
    { isEquivalence = equivalence
    }

  open IsEquivalence equivalence public

  ·-congˡ : LeftCongruent _≈_ _·_
  ·-congˡ y≈z = ·-cong refl y≈z

  ·-congʳ : RightCongruent _≈_ _·_
  ·-congʳ y≈z = ·-cong y≈z refl
    
record Group c ℓ : Set (Level.suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _·_
  infix  4 _≈_
  field
    Obj         : Set c
    _≈_         : Rel Obj ℓ
    _·_         : Op₂ Obj
    ϵ           : Obj
    _⁻¹         : Op₁ Obj
    isGroup     : IsGroup Obj _≈_ _·_ ϵ _⁻¹

  open IsGroup isGroup public
  

