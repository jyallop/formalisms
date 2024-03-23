open import lambda-calculus
open import Relation.Binary using (Setoid; IsEquivalence; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_ )
open import Level using (Level; _⊔_; suc)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_)

record IsCompatible {ℓ} (_~_ : Rel Λ ℓ) : Set (suc ℓ) where
  field
    left-application : {m n z : Λ} → m ~ n → (z · m) ~ (z · n)
    right-application : {m n z : Λ} → m ~ n → (m · z) ~ (n · z)
    abstraction : {m n : Λ} → {id : Id}  → m ~ n → (ƛ id ⇒ m) ~ (ƛ id ⇒ n)

record ReductionRelation ℓ : Set (suc ℓ) where
  field
    _~_ : Rel Λ ℓ
    isCompatible : IsCompatible _~_
    isReflexive : (m : Λ) → m ~ m
    isTransitive : {x y z : Λ} → x ~ y → y ~ z → x ~ z

data _→β_ : Λ → Λ → Set where
  β-ƛ : ∀ {x N M} → ((ƛ x ⇒ N) · M) →β (N [ x := M ])


beta : ReductionRelation _
beta = record
        { _~_ = _→β_ ;
          isCompatible = record
            { left-application = λ { {m} {n} {z} β-ƛ → {!β-ƛ {z · m} {z · n}!}  };
              right-application = {!!} ;
              abstraction = λ { {.((ƛ _ ⇒ _) · _)} {.(_ [ _ := _ ])} {id} β-ƛ → {!!} } }  ;
          isReflexive = λ { m → {!!}  };
          isTransitive = λ x x₁ → {!!} }

data _→ᵣ_ : Λ → Λ → Set where
