open import Level
open import Relation.Binary using (Rel)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Agda.Builtin.Equality using (_≡_; refl)

record Category {o l e : Level} (Obj : Set o) (_⇒_ : Rel Obj l) : Set (suc (o ⊔ l ⊔ e)) where
  eta-equality
  infix 4 _≈_ 
  infixr 9 _∘_

  field
    _≈_   : ∀ {A B} → Rel (A ⇒ B) e
    id    : ∀{A} → A ⇒ A
    _∘_   : ∀{A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

data One : Set where
  one : One

_=>_ : One → One → Set
_=>_ one = ｛ one ｝

one_cat : Category One _=>_
one_cat = record {
        _≈_ = _≡_;
        id = λ { {one} → refl };
        _∘_ = λ { {one} {one} {one} x x₁ → refl }
  }

open Category 

LeftCancellable : {n l : Level} → {Obj : Set n} → {_⇒_ : Rel Obj l} → (C : Category Obj _⇒_) → Set (suc (n ⊔ l))
LeftCancellable {n} {l} {Obj} {_⇒_} record { _≈_ = _≈_ ; id = id ; _∘_ = _∘_ } =
  {A B C : Obj} → {g h : A ⇒ B} → (f : B ⇒ C) → (f ∘ g) ≈ (f ∘ h) → (g ≈ h)

RightCancellable : {n l : Level} → {Obj : Set n} → {_⇒_ : Rel Obj l} → Category Obj _⇒_ → Set (suc (n ⊔ l))
RightCancellable {n} {l} {Obj} {_⇒_} record { _≈_ = _≈_ ; id = id ; _∘_ = _∘_ } =
  {A B C : Obj} → {g h : A ⇒ B} → (f : B ⇒ C) → (f ∘ g) ≈ (f ∘ h) → (g ≈ h)

record Monic {n l : Level} {Obj : Set n} {_⇒_ : Rel Obj l} (C : Category Obj _⇒_) : Set (suc (n ⊔ l)) where
  field
    isRightCancellable : LeftCancellable C

record Epic {n l : Level} {Obj : Set n} {_⇒_ : Rel Obj l} (C : Category Obj _⇒_) : Set (suc (n ⊔ l)) where 
  field
    isLeftCancellable : RightCancellable C
