open import Algebra using (Group; IsGroup; Obj)
open import Data.Nat

module PowerGroup {g₁ g₂} (G : Group g₁ g₂) where
  open Group G
  open import Relation.Binary.Reasoning.Setoid setoid

  _^_ : ∀ a → (n : ℕ) → Obj
  _ ^ ℕ.zero = ϵ
  a ^ (ℕ.suc x) = a · (a ^ x)


  power-law : ∀ {a b} → (n : ℕ) → (b · a · (b ⁻¹)) ^ n ≈ b · (a ^ n) · (b ⁻¹)
  power-law {a} {b} zero = begin
            ϵ
         ≡⟨ {!!} ⟩
            {!!}
         ∎
  power-law (ℕ.suc n) = {!!}
  power-law-two : ∀ {a b} → (n : ℕ) → (a · b) ^ n ≈ (a ^ n) · (b ^ n)
  power-law-three : ∀ {a} → a ^ 2 ≈ ϵ → ∃[ x ] x ^ 2 ≈ a

  power-law-four : ∀ {a} → a ^ 3 ≈ ϵ → ∃[ x ] x ^ 3 ≈ a

  power-law-five : ∀ {a} → ∃[ x ] x ^ 3 ≈ a ⁻¹ → ∃[ y ] y ^ 3 ≈ a
  power-law-six : ∀ {a b} → ∃[ x ] x · a · x ≈ b → ∃[ y ] y ^ 2 ≈ a · b
