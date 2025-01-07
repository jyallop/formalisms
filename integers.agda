open import Data.Nat using (ℕ; _+_; _*_; suc; zero; _^_)
open import Data.Nat.Properties using (+-assoc; *-distrib-+; *-identityʳ)
open import Data.Nat.Divisibility using (_∣_; n∣m*n)
open import Data.Nat.DivMod using (_/_; /-congˡ; m*n/n≡m; +-distrib-/-∣ˡ)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (_∈_; Pred)
open import Data.Product using (proj₁; proj₂)
open ≡-Reasoning

record Rational : Set₁ where
  field
    num : ℕ
    den : ℕ

+-congʳ : {x y z : ℕ} → x ≡ y → z + x ≡ z + y
+-congʳ refl = refl

+-congˡ : {x y z : ℕ} → x ≡ y → x + z ≡ y + z
+-congˡ refl = refl

*-congˡ : {x y z : ℕ} → x ≡ y → x * z ≡ y * z
*-congˡ refl = refl

series : ℕ → ℕ
series zero = zero
series n@(suc m) = (n ^ 2) + series m

lemma-one : (n : ℕ) → (series n) ≡ n * (n + 1) * (2 * n + 1) / 6
lemma-one zero = refl
lemma-one (suc n) = begin
          (suc n) ^ 2 + series n
    ≡⟨ +-congʳ {series n} {n * (n + 1) * (2 * n + 1) / 6} {(suc n) ^ 2} (lemma-one n) ⟩
          (suc n) ^ 2 + (n * (n + 1) * (2 * n + 1) / 6)
    ≡⟨ +-congʳ (/-congˡ (*-congˡ ((proj₁ *-distrib-+) n n 1))) ⟩
          (suc n) ^ 2 + ((((n * n) + (n * 1))) * (2 * n + 1)) / 6
    ≡⟨ +-congʳ (/-congˡ (*-congˡ (+-congʳ {n * 1} {n} {n * n} (*-identityʳ n)))) ⟩ 
          (suc n) ^ 2 + ((((n * n) + n)) * (2 * n + 1)) / 6
    ≡⟨ +-congˡ (sym (m*n/n≡m (suc (n * 1 + n * suc (n * 1))) 6 )) ⟩
          ((suc n) ^ 2) * 6 / 6 + ((((n * n) + n)) * (2 * n + 1)) / 6
    ≡⟨ sym (+-distrib-/-∣ˡ ((n * n + n) * (n + (n + zero) + 1))  (n∣m*n (suc (n * 1 + n * suc (n * 1))))) ⟩
          (((suc n) ^ 2) * 6 + (((n * n) + n)) * (2 * n + 1)) / 6
    ≡⟨ {!!} ⟩
          suc n * (suc n + 1) * (2 * suc n + 1) / 6
  ∎

