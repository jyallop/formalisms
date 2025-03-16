open import category
open import Agda.Builtin.Equality using (_≡_; refl)

module category.one where
-- We are going to define a simple set to test our relation
data One : Set where
  one : One

one-rel : One → One → Set
one-rel o1 o2 = one ≡ one

one-equivalence : Equivalence one-rel
one-equivalence = record { eq_refl = λ x → refl ; eq_transitive = λ r1 r2 → refl ; eq_symmetric = λ x → refl }

one-hom : One → One → Setoid
one-hom one one =
  record {
      carrier = one-rel one one
    ; _＝_ = λ { x y → x ≡ y }
    ; equivalence-relation = record { eq_refl = λ{ refl → refl }; eq_transitive = λ{ refl refl → refl }; eq_symmetric = λ{ refl → refl }}
    }

--The one object category with one arrow
one-cat : Category
one-cat = record
           { Obj = One
           ; hom = one-hom
           ; isCategory = record {
                        _∘_ = λ{ {one} {one} {one} refl refl → refl }
                      ; id = λ{ one → refl }
                      ; associative = λ{ {one} {one} {one} {one} {refl} {refl} {refl} → refl }
                      ; id-law-left = λ{ {one} {one} {refl} → refl }
                      ; id-law-right = λ{ {one} {one} {refl} → refl }
                      }
           }
