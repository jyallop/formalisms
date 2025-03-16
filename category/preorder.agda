open import category
open import Level

module category.preorder where

record Preoder {o : Level} : Set (suc (suc o)) where
  field
    Obj : Set o
    hom : Obj → Obj → Setoid {o}
    isCategory : IsCategory Obj hom
    --Here is the axiom of a preorder, to determine that there is only one function we just say there equal
    one-arrow : {A B : Obj} → {f g : ∣ hom A B ∣} → hom A B ~ f ＝ g
