open import category
open import Agda.Builtin.Equality using (_≡_; refl)

--here is a series of tests of some of our basic definitions
--to see if we can build things we'd expect and prove
--the corresponding properties about them

module category.tests where

data Two : Set where
  une : Two
  deux : Two

data two-relation : Two → Two → Set where
  une-une : two-relation une une
  une-deux : two-relation une deux
  deux-deux : two-relation deux deux

two-relation-setoid : Two → Two → Setoid
two-relation-setoid x y = record {
    carrier = two-relation x y
  ; _＝_ = λ{ x y → x ≡ y }
  ; equivalence-relation = record {
      eq_refl = λ{ une-une → refl ; une-deux → refl ; deux-deux → refl }
    ; eq_transitive = λ{ refl refl → refl }
    ; eq_symmetric = λ{ refl → refl }
    }
  }

two-cat : Category
two-cat = record
           { Obj = Two
           ; hom = two-relation-setoid
           ; _∘_ = λ{ g une-une → g ; deux-deux une-deux → une-deux ; deux-deux deux-deux → deux-deux }
           ; id = λ{ une → une-une ; deux → deux-deux }
           ; associative = λ{ {A} {B} {C} {D} {une-une} {une-une} {une-une} → refl
             ; {A} {B} {C} {D} {une-une} {une-une} {une-deux} → refl
             ; {A} {B} {C} {D} {une-une} {une-deux} {deux-deux} → refl
             ; {A} {B} {C} {D} {une-deux} {deux-deux} {deux-deux} → refl
             ; {A} {B} {C} {D} {deux-deux} {deux-deux} {deux-deux} → refl }
           ; id-law-left = λ { {une} {une} {une-une} → refl ; {une} {deux} {une-deux} → refl ; {deux} {deux} {deux-deux} → refl }
           ; id-law-right = λ { {une} {une} {une-une} → refl ; {une} {deux} {une-deux} → refl ; {deux} {B} {deux-deux} → refl }
           }

-- We are going to build a slightly stranger relation for fun and to test our definition 
data Three : Set where
  uno : Three
  dos : Three
  tres : Three

data three-relation : Three → Three → Set where
  one-one : three-relation uno uno
  one-three : three-relation uno tres
  two-two : three-relation dos dos
  three-three : three-relation tres tres
  three-one : three-relation tres uno

-- Proving that our relation is an equivalence should just be some functions that are
-- easily broken up into case statements
three-reflexive : reflexive three-relation
three-reflexive = λ { uno → one-one; dos → two-two; tres → three-three}

three-transitive : transitive three-relation three-relation three-relation
three-transitive one-one one-one = one-one
three-transitive one-one one-three = one-three
three-transitive one-three three-three = one-three
three-transitive one-three three-one = one-one
three-transitive two-two two-two = two-two
three-transitive three-three three-three = three-three
three-transitive three-three three-one = three-one
three-transitive three-one one-one = three-one
three-transitive three-one one-three = three-three

three-symmetric : symmetric three-relation three-relation
three-symmetric one-one = one-one
three-symmetric one-three = three-one
three-symmetric two-two = two-two
three-symmetric three-three = three-three
three-symmetric three-one = one-three

-- Finally the full structure of our equivalence relation
three-equivalence : Equivalence three-relation
three-equivalence = record {
    eq_refl = three-reflexive
  ; eq_transitive = three-transitive
  ; eq_symmetric = three-symmetric
  }

data One : Set where
  one : One

one-rel : One → One → Set
one-rel o1 o2 = one ≡ one

one-equivalence : Equivalence one-rel
one-equivalence = record { eq_refl = λ x → refl ; eq_transitive = λ r1 r2 → refl ; eq_symmetric = λ x → refl }


-- A test of our setoid using the one set
one-setoid : Setoid
one-setoid = record {
    carrier = One
  ; _＝_ = one-rel
  ; equivalence-relation = one-equivalence
  }


-- A test of our setoid construction using the three set
three-setoid : Setoid 
three-setoid = record { carrier = Three
  ; _＝_ = λ x y → three-relation x y
  ; equivalence-relation = three-equivalence
  }

-- A simple test of our construction
test-map : Map three-setoid one-setoid
test-map = record {
      map = λ x → one
    ; map-law = λ x → refl
    }

test-ext : test-map ≡ test-map
test-ext = extensionality λ { x → refl } 


