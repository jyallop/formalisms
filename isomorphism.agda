open import Relation.Binary using (Setoid; IsEquivalence; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_ )
open import Level using (Level; _⊔_; suc)
open import category

--This file needs the changes to the defintion of category to be finished before it can be loaded again
record Equivalence {n : Level} (A : Set n) (_≈_ : Rel A (suc n)) : Set (suc (suc n)) where
  field
    reflexive : ∀ a → a ≈ a
    symmetric : ∀ a b → a ≈ b → b ≈ a
    transitive : ∀ a b c → a ≈ b → b ≈ c → a ≈ c

LeftCancellable : {n l : Level} → {Obj : Set n} → {_⇒_ : Rel Obj l} → (C : Category Obj _⇒_) → Set (suc (n ⊔ l))
LeftCancellable {n} {l} {Obj} {_⇒_} record { _≈_ = _≈_ ; id = id ; _∘_ = _∘_ } =
  {A B C : Obj} → {g h : A ⇒ B} → (f : B ⇒ C) → (f ∘ g) ≈ (f ∘ h) → (g ≈ h)

RightCancellable : {n l : Level} → {Obj : Set n} → {_⇒_ : Rel Obj l} → Category Obj _⇒_ → Set (suc (n ⊔ l))
RightCancellable {n} {l} {Obj} {_⇒_} record { _≈_ = _≈_ ; id = id ; _∘_ = _∘_ } =
  {A B C : Obj} → {g h : A ⇒ B} → (f : B ⇒ C) → (f ∘ g) ≈ (f ∘ h) → (g ≈ h)

record Monic {n l : Level} {Obj : Set n} {_⇒_ : Rel Obj l} (C : Category Obj _⇒_) : Set (suc (n ⊔ l)) where
  field
    isRightCancellable : RightCancellable C

record Epic {n l : Level} {Obj : Set n} {_⇒_ : Rel Obj l} (C : Category Obj _⇒_) : Set (suc (n ⊔ l)) where 
  field
    isLeftCancellable : LeftCancellable C

record Isomorphism {n l : Level} {Obj : Set n} {_⇒_ : Rel Obj l} (C : Category Obj _⇒_) : Set (suc (n ⊔ l)) where
  field
    isLeftCancellable : LeftCancellable C
    isRightCancellable : RightCancellable C
