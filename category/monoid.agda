open import Data.Nat.Base using (ℕ; zero; _+_)
open import category
open import category.examples

module category.monoid where

data n-type : ℕ → ℕ → Set where
  arrow-label : {n : ℕ} → n-type n n

arrow-equivalence : Equivalence n-type
arrow-equivalence = record { eq_refl = λ x → arrow-label ; eq_transitive = λ{ arrow-label arrow-label → arrow-label }; eq_symmetric = λ{ arrow-label → arrow-label }}

n-setoid : One → One → Setoid
n-setoid one one =
  record {
      carrier = ℕ
    ; _＝_ = λ{ x y → n-type x y }
    ; equivalence-relation = arrow-equivalence
    }

arrow-label-cong : {n m : ℕ} → n-setoid one one ~ n ＝ m → n-setoid one one ~ ℕ.suc n ＝ ℕ.suc m
arrow-label-cong arrow-label = arrow-label

integers : Category
integers = record
            { Obj = One
            ; hom = n-setoid
            ; _∘_ = λ{ {one} {one} {one} g f → f + g }
            ; id = λ{ one → ℕ.zero }
            ; associative = λ{ {one} {one} {one} {one} {f} {g} {h} → helper-one f g h }
            ; id-law-left = λ{ {one} {one} {f} → helper-two f }
            ; id-law-right = λ{ {one} {one} {f} → arrow-label }
            }
          where
            helper-one : (f g h : ∣ n-setoid one one ∣) → n-setoid one one ~ f + (g + h) ＝ (f + g + h)
            helper-one ℕ.zero g h = arrow-label
            helper-one (ℕ.suc f) g h = arrow-label-cong (helper-one f g h)
            helper-two : (f : ∣ n-setoid one one ∣) → n-setoid one one ~ f + ℕ.zero ＝ f
            helper-two ℕ.zero = arrow-label
            helper-two (ℕ.suc f) = arrow-label-cong (helper-two f)

