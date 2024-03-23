open import lambda-calculus
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum

record Combinator : Set where
  field
    term : Λ
    closed : Empty FV⟨ term ⟩

I : {x : Id} → Combinator 
I {x} = record {
    term = ƛ x ⇒ ` x
  ; closed = λ x → λ { (refl , snd) → snd refl }
  }

K : {x y : Id} → Combinator
K {x} {y} = record { term = ƛ x ⇒ (ƛ y ⇒ ` x) ; closed = λ { x ((fst , snd₁) , snd) → snd fst } }

S : {x y z : Id} → Combinator
S {x} {y} {z} = record {
  term = ƛ x ⇒ (ƛ y ⇒ (ƛ z ⇒ (` x · ` z · (` y · ` z)))) ;
  closed = λ { id (((inj₁ (inj₁ x) , snd₂) , snd₁) , snd) → snd x ;
               id (((inj₁ (inj₂ y) , snd₂) , snd₁) , snd) → snd₂ y ;
               id (((inj₂ (inj₁ x) , snd₂) , snd₁) , snd) → snd₁ x ;
               id (((inj₂ (inj₂ y) , snd₂) , snd₁) , snd) → snd₂ y
               }
  }
