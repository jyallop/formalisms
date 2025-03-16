open import Data.Nat using (ℕ; zero; _+_)
open import Data.Nat.Properties using (+-comm; +-assoc)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import category
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level

module category.monoid where

data One {o : Level} : Set o where
  one : One

record Monoid {o : Level} : Set (suc (suc (suc o))) where
  field
    M : Set o
    op : M → M → M
    _＝_ : M → M → Set o
    ＝-equiv : Equivalence _＝_
    e : M
    op-assoc : (x y z : M) → op (op x y) z ＝ op x (op y z)
    id-right : (x : M) → op x e ＝ x
    id-left : (x : M) → op e x ＝ x
  isCategory : Category
  isCategory = record {
      Obj = One
    ; hom = λ _ _ → record { carrier = M ; _＝_ = λ x y → x ＝ y ; equivalence-relation = ＝-equiv }
    ; isCategory = record
                    { _∘_ = λ g f → op g f
                    ; id = λ A → e
                    ; associative = λ {A} {B} {C} {D} {f} {g} {h} → op-assoc h g f
                    ; id-law-left = λ {A} {B} {f} → id-left f
                    ; id-law-right = λ {A} {B} {f} → id-right f
                    }
    }

integers : Monoid
integers = record {
               M = ℕ
             ; op = _+_
             ; _＝_ = λ x y → x ≡ y
             ; ＝-equiv = record {
                 eq_refl = λ x → refl
               ; eq_transitive = λ{ refl refl → refl }
               ; eq_symmetric = λ{ refl → refl }
               }
             ; e = 0
             ; op-assoc = λ x y z → +-assoc x y z
             ; id-right = λ x → +-comm x 0
             ; id-left = λ x → refl
             }

