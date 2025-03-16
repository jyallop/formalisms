open import category
open import Level
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; _+_)

module category.discrete where

record Discrete {o : Level} : Set (suc (suc o)) where
  open IsCategory
  field
    Obj : Set o
  --For the discrete category we construct the hom
  --for the hom, the only arrow is equality
  hom : Obj → Obj → Setoid {o}
  hom = λ x y → record { carrier = x ≡ y ;
    _＝_ = λ x y → x ≡ y ;
    equivalence-relation =
      record { eq_refl = λ{ x → refl } ; eq_transitive = λ{ refl refl → refl }; eq_symmetric = λ{ refl → refl } } }
  field
    isCategory : IsCategory Obj hom

--Let's see if we can construct the discrete category
--where are objects are the naturals and the only arrows
--are the identities
discrete-naturals : Discrete
discrete-naturals = record { Obj = ℕ ; isCategory = record
                                                     { _∘_ = λ{ refl refl → refl }
                                                     ; id = λ A → refl
                                                     ; associative = λ{ {A} {B} {C} {D} {refl} {refl} {refl} → refl }
                                                     ; id-law-left = λ{ {A} {B} {refl} → refl }
                                                     ; id-law-right = λ{ {A} {B} {refl} → refl }
                                                     } }
