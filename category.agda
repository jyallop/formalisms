open import Level
open import Relation.Binary using (Rel)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

-- I am in the process of reworking the definition of a Category 
-- based on the following "Constructive Category Theory" by Huet
-- The definition in that paper starts with binary relations so we give the following defintions
-- Defines a binary relation
R : {a b : Level} → Set a → Set b → Set (suc a ⊔ suc b)
R {a} {b} A B = A → B → Set (a ⊔ b)

reflexive : {a : Level} {A : Set a} → R A A → Set a
reflexive {a} {A} r = (x : A) → r x x

transitive : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → R A B → R B C → R A C → Set (a ⊔ b ⊔ c)
transitive {_} {_} {_} {A} {B} {C} r1 r2 r3 = {a : A} → {b : B} → {c : C} → r1 a b → r2 b c → r3 a c

symmetric : {a b : Level} {A : Set a} {B : Set b} → R A B → R B A → Set (a ⊔ b)
symmetric {_} {_} {A} {B} r1 r2 = {a : A} → {b : B} → r1 a b → r2 b a

record Equivalence {a : Level} {A : Set a} (r : R A A) : Set (suc a) where
   field
     eq_refl : reflexive λ A A → r A A 
     eq_transitive : transitive (λ A B → r A B) (λ B C → r B C) λ A C → r A C 
     eq_symmetric : symmetric (λ A B → r A B) λ B A → r B A 

record PartialEquivalence {a l : Level} {A : Set a} (r : R A A) : Set (suc (a ⊔ l)) where
  field
     eq_refl : reflexive λ A A → r A A
     eq_transitive : transitive (λ A B → r A B) (λ B C → r B C) λ A C → r A C 

-- Definition of a setoid, the object that will contain arrows in our category
record Setoid {l : Level} : Set (suc l) where
  infix 4 _＝_ 
  field
    carrier : Set l
    _＝_ : R carrier carrier
    equivalence-relation : Equivalence _＝_

-- This syntax was taken from "Category theoretic structure of setoids" by Kinoshita et al
∣_∣ : {l : Level} → Setoid {l} → Set l
∣ x ∣ = Setoid.carrier x

_~_＝_ : {l : Level} → (A : Setoid {l}) → R ∣ A ∣ ∣ A ∣
_~_＝_ A x y = (A Setoid.＝ x) y

-- Now we need to define the setoid of maps
record Map {a b : Level} (A : Setoid {a}) (B : Setoid {b}) : Set (suc (a ⊔ b)) where
  open Setoid
  field
    map : ∣ A ∣ → ∣ B ∣
    map-law : {x y : ∣ A ∣} → (A ~ x ＝ y) → (B ~ (map x) ＝ (map y))

open Map
-- We are going to use functional extensionality as our definition of equality for maps (and make them definitionally equal)
-- According to Philip Wadler this should be fine, so ¯\_(ツ)_/¯
-- The fine thing being that two maps that are pointwise equal are definitionally equal
-- not the idea of functional extensionality itself
-- (We just won't define insertion sort and merge sort as maps :))
postulate
  extensionality : {a b : Level} → {A : Setoid {a}} → {B : Setoid {b}} → {f g : Map A B} → (∀ (x : ∣ A ∣) → B ~ (map f x) ＝ (map g x)) → f ≡ g

map-setoid : {a b : Level} → Setoid {a} → Setoid {b} → Setoid {suc a ⊔ suc b}
map-setoid A B =
    record {
        carrier = Map A B
      ; _＝_ = _≡_
      ; equivalence-relation = record { eq_refl = λ x → refl ; eq_transitive = λ { refl refl → refl } ; eq_symmetric = λ { refl → refl } }
      }

_⇒_ : {a b : Level} → (A : Setoid {a}) → (B : Setoid {b}) → Setoid {suc a ⊔ suc b}
A ⇒ B = map-setoid A B

record IsCategory {o : Level} (Obj : Set o) (hom : Obj → Obj → Setoid {o}) : Set (suc o) where
  infix 9 _∘_
  field
    _∘_ : {A B C : Obj} → (g : ∣ hom B C ∣) → (f : ∣ hom A B ∣) → ∣ (hom A C) ∣
    id : (A : Obj) → ∣ (hom A A) ∣
    associative : {A B C D : Obj} {f : ∣ hom A B ∣} {g : ∣ hom B C ∣} {h : ∣ hom C D ∣} → hom A D ~ ((h ∘ g) ∘ f) ＝ (h ∘ (g ∘ f))
    id-law-left : {A B : Obj} {f : ∣ hom A B ∣} → hom A B ~ ((id B) ∘ f) ＝ f
    id-law-right : {A B : Obj} {f : ∣ hom A B ∣ } → hom A B ~ (f ∘ (id A)) ＝ f

record Category {o : Level} : Set (suc (suc o)) where
  eta-equality
  open Setoid
  field
    Obj : Set o
    hom : Obj → Obj → Setoid {o}
    isCategory : IsCategory Obj hom
