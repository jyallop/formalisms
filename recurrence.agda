open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as L using (Level; _⊔_; suc) 
open import Data.Nat.Base
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool using (true; false)

record Recurrence {n : Level} : Set (L.suc n) where
  field
    domain : Set n
    parameters : domain
    index_mapping : domain → domain
    functions : _

N₁ N₂ N₃ : ℕ
N₁ = 10
N₂ = 11
N₃ = 12

X : ℕ → ℕ → ℕ → ℕ
X₁̣₁ : ℕ → ℕ → ℕ → ℕ
X₂̣₁ : ℕ → ℕ → ℕ → ℕ
Y₁̣₁ : ℕ → ℕ → ℕ → ℕ
Y₁̣₂ : ℕ → ℕ → ℕ → ℕ

X₁̣₁ 1 1 1 = X N₁ N₂ N₃
X₁̣₁ 1 1 x = X₂̣₁ 1 1 x
X₁̣₁ 1 p₁ p₂ = Y₁̣₁ 1 (p₁ - 1) p₂
X₁̣₁ p₁ p₂ p₃ = Y₁̣₁ (p₁ - 1) p₂ p₃

Y₁̣₁ 1 1 1 = 0
Y₁̣₁ p₁ p₂ 1 = Y₁̣₂ p₁ p₂ 1
Y₁̣₁ p₁ p₂ p₃ = X₁̣₁ p₁ p₂ (p₃ - 1)

X₂̣₁ _ _ _ = 0

Y₁̣₂ _ _ _ = 0

X p₁ p₂ p₃ with p₁ == N₁ | p₂ == N₂ | p₃ == N₃
... | true | true | true = X₁̣₁ p₁ p₂ p₃
... |  _   |  _   |  _   = 0
--X₁̣₁ N₁ N₂ N₃
--X _ _ _ = 0


