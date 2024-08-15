open import Data.String using (String; _==_; _≟_)

data Type : Set where
  atomic : String → Type
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type

data Term : Type → Set where
  var : (A : Type) → Term A
  ⟨_,_⟩ : {A B : Type} → Term A → Term B → Term (A × B)

π¹_ : {A B : Type} → Term (A × B) → Term B
π¹ var .(_ × _) = {!!}
π¹ ⟨ x , x₁ ⟩ = x₁





  

--weak-normalization : Set 
