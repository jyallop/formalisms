open import category
open import Agda.Builtin.Equality using (_≡_; refl)

--Building the Category with two objects
module category.two where


data Two : Set where
  one : Two
  two : Two

data two-relation : Two → Two → Set where
  one-one : two-relation one one
  one-two : two-relation one two
  two-two : two-relation two two

two-relation-setoid : Two → Two → Setoid
two-relation-setoid x y = record {
    carrier = two-relation x y
  ; _＝_ = λ{ x y → x ≡ y }
  ; equivalence-relation = record {
      eq_refl = λ{ one-one → refl ; one-two → refl ; two-two → refl }
    ; eq_transitive = λ{ refl refl → refl }
    ; eq_symmetric = λ{ refl → refl }
    }
  }

two-cat : Category
two-cat = record
           { Obj = Two
           ; hom = two-relation-setoid
           ; _∘_ = λ{ g one-one → g ; two-two one-two → one-two ; two-two two-two → two-two }
           ; id = λ{ one → one-one ; two → two-two }
           ; associative = λ{ {A} {B} {C} {D} {one-one} {one-one} {one-one} → refl
             ; {A} {B} {C} {D} {one-one} {one-one} {one-two} → refl
             ; {A} {B} {C} {D} {one-one} {one-two} {two-two} → refl
             ; {A} {B} {C} {D} {one-two} {two-two} {two-two} → refl
             ; {A} {B} {C} {D} {two-two} {two-two} {two-two} → refl }
           ; id-law-left = λ { {one} {one} {one-one} → refl ; {one} {two} {one-two} → refl ; {two} {two} {two-two} → refl }
           ; id-law-right = λ { {one} {one} {one-one} → refl ; {one} {two} {one-two} → refl ; {two} {B} {two-two} → refl }
           }
