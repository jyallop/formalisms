open import Algebra using (Group; Op₂; IsGroup; Op₁)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel)

record IsAbelian {c} {ℓ} (Obj : Set c) (_≈_ : Rel Obj ℓ) (_·_ : Op₂ Obj) (ϵ : Obj) (_⁻¹ : Op₁ Obj) : Set (Level.suc (c ⊔ ℓ)) where
  field
    commutative : {x y : Obj} → (x · y) ≈ (y · x)
    isGroup     : IsGroup _≈_ _·_ ϵ _⁻¹
  open IsGroup isGroup public    

record Abelian c ℓ : Set (Level.suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _·_
  infix  4 _≈_
  field
    Obj         : Set c
    _≈_         : Rel Obj ℓ
    _·_         : Op₂ Obj
    ϵ           : Obj
    _⁻¹         : Op₁ Obj
    isAbelian   : IsAbelian Obj _≈_ _·_ ϵ _⁻¹

  open IsAbelian isAbelian public

module AbelianProperties {g₁ g₂} (G : Abelian g₁ g₂) where
  open Abelian G

  open import Relation.Binary.Reasoning.Setoid setoid

  inverses-commute : {a b : Obj} → a ⁻¹ · b ⁻¹ ≈ b ⁻¹ · a ⁻¹
  inverses-commute = commutative 

  
