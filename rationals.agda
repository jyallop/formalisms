open import Data.Nat.Base using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

record ℚ : Set where
  field
    num : ℕ
    den : ℕ
    den≠0 : ¬ (den ≡ 0)

_*_ : ℚ → ℚ → ℚ
record { num = num₁ ; den = den₁ ; den≠0 = den≠1 } *
  record { num = num ; den = den ; den≠0 = den≠0 } = record {
  num = num₁ Data.Nat.Base.* num ;
  den = den₁ Data.Nat.Base.* den ;
  den≠0 = {!!}
  }

1/2 : ℚ
1/2 = record {
    num = 1
  ; den = 2
  ; den≠0 = λ{ () }
  }
