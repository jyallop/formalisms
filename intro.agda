open import Level using (Level; _⊔_; suc; 0ℓ)
open import Algebra.Bundles using (Magma)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Core using (Rel)
open import Algebra.Definitions using (Congruent₂)
open import Algebra.Core

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

data Color : Set where
  Red : Color
  Blue : Color

fun : Op₂ Color
fun Red _ = Red
--fun Blue Red = Red
--fun Red Blue = Blue
fun Blue _ = Blue


eq : Rel Color _
eq x y = x ≡ y

eqRefl : Reflexive eq
eqRefl = refl

eqSym : Symmetric eq
eqSym refl = refl

eqTrans : Transitive eq
eqTrans refl refl = refl

fun-cong : Congruent₂ eq fun
fun-cong refl refl = refl

eqEquivalence : IsEquivalence eq
eqEquivalence = record {
  refl = refl;
  sym = λ { refl → refl };
  trans = eqTrans
  }

color : Magma 0ℓ 0ℓ
color = record {
        Carrier = Color;
        _≈_ = eq;
        _∙_ = fun;
        isMagma = record { isEquivalence = eqEquivalence ;
                           ∙-cong = fun-cong }
        }


trans-≡ : {n : Level} {A : Set n} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans-≡ refl refl = refl

reflexivity : {n : Level} → {A : Set n} → {x y : A} → x ≡ y → y ≡ x
reflexivity refl = refl


record Σ {a b : Level} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

projection : {b : Level} → {A : Set} {B : A → Set b} → Σ A B → A
projection (fst , snd) = fst

