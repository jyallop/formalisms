open import lambda-calculus
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum
open import Relation.Nullary using (¬_)

record Combinator : Set where
  field
    term : Λ
    closed : Empty FV⟨ term ⟩

Icom : {x : Id} → Combinator 
Icom {x} = record {
    term = ƛ x ⇒ ` x
  ; closed = λ x → λ { (refl , snd) → snd refl }
  }

Kcom : {x y : Id} → Combinator
Kcom {x} {y} = record { term = ƛ x ⇒ (ƛ y ⇒ ` x) ; closed = λ { x ((fst , snd₁) , snd) → snd fst } }

S : {x y z : Id} → Combinator
S {x} {y} {z} = record {
  term = ƛ x ⇒ (ƛ y ⇒ (ƛ z ⇒ (` x · ` z · (` y · ` z)))) ;
  closed = λ { id (((inj₁ (inj₁ x) , snd₂) , snd₁) , snd) → snd x ;
               id (((inj₁ (inj₂ y) , snd₂) , snd₁) , snd) → snd₂ y ;
               id (((inj₂ (inj₁ x) , snd₂) , snd₁) , snd) → snd₁ x ;
               id (((inj₂ (inj₂ y) , snd₂) , snd₁) , snd) → snd₂ y
               }
  }


I : {x : Id} → Λ
I {x} = ƛ x ⇒ ` x

K : {x y : Id} → Λ
K {x} {y} = ƛ x ⇒ (ƛ y ⇒ ` x)

consistent-I-K : ¬ (Con I K)
consistent-I-K (consistent prop A B x) = {!!}
