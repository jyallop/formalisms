open import Data.Nat using (ℕ; _+_; _*_; suc; zero; _^_)
open import Data.Nat.DivMod using (_/_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Rational : Set₁ where
  field
    num : ℕ
    den : ℕ

series : ℕ → ℕ
series zero = zero
series n@(suc m) = (n ^ 2) + series m

+-rcong : {x y z : ℕ} → x ≡ y → z + x ≡ z + y
+-rcong refl = refl

lemma-one : (n : ℕ) → (series n) ≡ n * (n + 1) * (2 * n + 1) / 6
lemma-one zero = refl
lemma-one (suc n) = begin
          (suc n) ^ 2 + series n
    ≡⟨ +-rcong {series n} {n * (n + 1) * (2 * n + 1) / 6} {(suc n) ^ 2} (lemma-one n) ⟩
      (suc n) ^ 2 + (n * (n + 1) * (2 * n + 1) / 6)
    ≡⟨ {!!} ⟩
    {!!}
  ∎
