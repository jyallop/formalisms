open import category using (Category)
open import Level
open import Relation.Binary using (Rel)

module arrow-properties {o l e : Level} {Obj : Set o} {_⇒_ : Rel Obj l} (C : Category Obj _⇒_) where
  open Category C

  record IsMonic {A B : Obj} (f : A ⇒ B) : Set (suc (o ⊔ l)) where
    field
      left-cancellable : {C : Obj} (g h : C ⇒ A) → (f ∘ g ≈ f ∘ h) → g ≈ h

  composition-monic : {A B C : Obj} (f : B ⇒ C) → (g : A ⇒ B) → IsMonic f → IsMonic g → IsMonic (f ∘ g)
  composition-monic f g f-monic g-monic = record {
    left-cancellable = λ h₁ h₂ x → {! associative x!}
    }

  monic-composition : {A B C : Obj} (f : B ⇒ C) → (g : A ⇒ B) → IsMonic (f ∘ g) → IsMonic f 
  monic-composition f g comp-monic = {!!}
