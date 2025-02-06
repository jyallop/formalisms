open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty; _⊂_; U)
open import Relation.Binary using (Rel; DecidableEquality)
open import Level using (Level; 0ℓ)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Agda.Builtin.Equality using (_≡_; refl)

private
  lemma-two : {x y : ℕ} → suc x ≡ suc y → x ≡ y
  lemma-two refl = refl

_≡ᵢ_ : DecidableEquality ℕ
zero ≡ᵢ zero = true Relation.Nullary.because Relation.Nullary.ofʸ refl
zero ≡ᵢ suc y = false Relation.Nullary.because (Relation.Nullary.ofⁿ (λ{ () }))
suc x ≡ᵢ zero = false Relation.Nullary.because (Relation.Nullary.ofⁿ (λ{ () }))
suc x ≡ᵢ suc y with x ≡ᵢ y
... | no ¬a = false Relation.Nullary.because (Relation.Nullary.ofⁿ λ x₁ → ¬a (lemma-two x₁))
... | yes a = true Relation.Nullary.because (Relation.Nullary.ofʸ (lemma-one a))
  where
    lemma-one : x ≡ y → suc x ≡ suc y
    lemma-one refl = refl

-- Unless the lambda term is literally infinite this will terminate
{-# TERMINATING #-}
new-identifier : {l : Level} → ℕ → (p : Pred ℕ l) → Decidable p →  Σ[ x ∈ ℕ ] x ∉ p
new-identifier n p prop with prop n
... | no ¬a = n , ¬a
... | true Relation.Nullary.because proof = new-identifier (suc n) p prop

open import lambda-calculus ℕ _≡ᵢ_ (new-identifier 0) 0 public
