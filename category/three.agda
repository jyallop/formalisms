open import category
open import Agda.Builtin.Equality using (_≡_; refl)

module category.three where
-- We are going to build a slightly stranger relation for fun and to test our definition 
data Three : Set where
  one : Three
  two : Three
  three : Three

-- We are going to build the set of homs in a slightly different way out of curiousity
-- This is how we would do it based on the defition of the relations for one and two
data three-relation : Three → Three → Set where
  one-one : three-relation one one
  one-three : three-relation one three
  two-two : three-relation two two
  three-three : three-relation three three
  two-three : three-relation two three

--We are going to try to define it more directly by giving different defitions for each
--hom
data one-hom : Three → Set where
  one-to-one : one-hom one
  one-to-two : one-hom two
  one-to-three : one-hom three

data two-hom : Three → Set where
  two-to-two : two-hom two
  two-to-three : two-hom three

data three-hom : Three → Set where
  three-to-three : three-hom three

three-hom-setoid : Three → Three → Setoid
three-hom-setoid one y = record {
    carrier = one-hom y
  ; _＝_ = _≡_
  ; equivalence-relation = record {
      eq_refl = λ x → refl
    ; eq_transitive = λ{ refl refl → refl }
    ; eq_symmetric = λ{ refl → refl }
    }
  }
three-hom-setoid two y = record {
    carrier = two-hom y
  ; _＝_ = _≡_
  ; equivalence-relation = record {
      eq_refl = λ{ x → refl }
    ; eq_transitive = λ{ refl refl → refl }
    ; eq_symmetric = λ{ refl → refl }
    }
  }
three-hom-setoid three y = record {
    carrier = three-hom y
  ; _＝_ = _≡_
  ; equivalence-relation = record {
      eq_refl = λ x → refl
    ; eq_transitive = λ{ refl refl → refl }
    ; eq_symmetric = λ{ refl → refl }
    }
  }

three-category : Category
three-category = record {
    Obj = Three
  ; hom = three-hom-setoid
  ; isCategory = record {
    _∘_ = λ{
          {one} {one} {one} g f → one-to-one
        ; {one} {one} {C} g f → g
        ; {one} {two} {two} g f → one-to-two
        ; {one} {two} {three} g f → one-to-three
        ; {one} {three} {three} g f → one-to-three
        ; {two} {two} {C} g f → g 
        ; {two} {three} {three} g f → two-to-three
        ; {three} {three} {three} g f → three-to-three
        }
    ; id = λ{ one → one-to-one ; two → two-to-two ; three → three-to-three }
    ; associative = λ{
        {one} {one} {one} {one} {f} {g} {h} → refl
      ; {one} {one} {one} {two} {f} {g} {h} → refl
      ; {one} {one} {one} {three} {f} {g} {h} → refl
      ; {one} {one} {two} {two} {f} {g} {h} → refl
      ; {one} {one} {two} {three} {f} {g} {h} → refl
      ; {one} {one} {three} {three} {f} {g} {h} → refl
      ; {one} {two} {two} {two} {f} {g} {h} → refl
      ; {one} {two} {two} {three} {f} {g} {h} → refl
      ; {one} {two} {three} {three} {f} {g} {h} → refl
      ; {one} {three} {three} {three} {f} {g} {h} → refl
      ; {two} {two} {C} {D} {f} {g} {h} → refl
      ; {two} {three} {three} {three} {f} {g} {h} → refl
      ; {three} {three} {three} {three} {f} {g} {h} → refl
      }
    ; id-law-left = λ{
        {one} {one} {one-to-one} → refl
      ; {one} {two} {one-to-two} → refl
      ; {one} {three} {one-to-three} → refl
      ; {two} {two} {two-to-two} → refl
      ; {two} {three} {two-to-three} → refl
      ; {three} {three} {three-to-three} → refl
      }
    ; id-law-right = λ{
        {one} {one} {one-to-one} → refl
      ; {one} {two} {one-to-two} → refl
      ; {one} {three} {one-to-three} → refl
      ; {two} {two} {two-to-two} → refl
      ; {two} {three} {f} → refl
      ; {three} {three} {three-to-three} → refl
      }
    }
  }
    
