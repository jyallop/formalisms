open import Level
open import Relation.Binary using (Rel)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; _+_)
open import Data.Nat.Properties using (+-comm)

-- I am in the process of reworking the definition of a Category 
-- based on the following "Constructive Category Theory" by Huet
-- The definition in that paper starts with binary relations so we give the following defintions
-- Defines a binary relation
R : {a b : Level} → Set a → Set b → Set (suc a ⊔ suc b)
R {a} {b} A B = A → B → Set (a ⊔ b)

reflexive : {a : Level} {A : Set a} → R A A → Set _
reflexive {a} {A} r = (x : A) → r x x

transitive : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → R A B → R B C → R A C → Set _
transitive {_} {_} {_} {A} {B} {C} r1 r2 r3 = {a : A} → {b : B} → {c : C} → r1 a b → r2 b c → r3 a c

symmetric : {a b : Level} {A : Set a} {B : Set b} → R A B → R B A → Set _
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

-- We are going to define a simple set to test our relation
data One : Set where
  one : One

one-rel : One → One → Set
one-rel o1 o2 = one ≡ one

one-equivalence : Equivalence one-rel
one-equivalence = record { eq_refl = λ x → refl ; eq_transitive = λ r1 r2 → refl ; eq_symmetric = λ x → refl }

-- We are going to build a slightly stranger relation for fun and to test our definition 
data Three : Set where
  uno : Three
  dos : Three
  tres : Three

data three-relation : Three → Three → Set where
  one-one : three-relation uno uno
  one-three : three-relation uno tres
  two-two : three-relation dos dos
  three-three : three-relation tres tres
  three-one : three-relation tres uno

-- Proving that our relation is an equivalence should just be some functions that are
-- easily broken up into case statements
three-reflexive : reflexive three-relation
three-reflexive = λ { uno → one-one; dos → two-two; tres → three-three}

three-transitive : transitive three-relation three-relation three-relation
three-transitive one-one one-one = one-one
three-transitive one-one one-three = one-three
three-transitive one-three three-three = one-three
three-transitive one-three three-one = one-one
three-transitive two-two two-two = two-two
three-transitive three-three three-three = three-three
three-transitive three-three three-one = three-one
three-transitive three-one one-one = three-one
three-transitive three-one one-three = three-three

three-symmetric : symmetric three-relation three-relation
three-symmetric one-one = one-one
three-symmetric one-three = three-one
three-symmetric two-two = two-two
three-symmetric three-three = three-three
three-symmetric three-one = one-three

-- Finally the full structure of our equivalence relation
three-equivalence : Equivalence three-relation
three-equivalence = record {
    eq_refl = three-reflexive
  ; eq_transitive = three-transitive
  ; eq_symmetric = three-symmetric
  }

-- Definition of a setoid, the object that will contain arrows in our category
record Setoid {l : Level} : Set (suc l) where
  infix 4 _＝_ 
  field
    carrier : Set l
    _＝_ : R carrier carrier
    equivalence-relation : Equivalence _＝_

-- A test of our setoid using the one set
one-setoid : Setoid
one-setoid = record {
    carrier = One
  ; _＝_ = one-rel
  ; equivalence-relation = one-equivalence
  }

-- A test of our setoid construction using the three set
three-setoid : Setoid 
three-setoid = record { carrier = Three
  ; _＝_ = λ x y → three-relation x y
  ; equivalence-relation = three-equivalence
  }

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

-- A simple test of our construction
test-map : Map three-setoid one-setoid
test-map = record {
      map = λ x → one
    ; map-law = λ x → refl
    }


open Map
-- We are going to use functional extensionality as our definition of equality for maps (and make them definitionally equal)
-- According to Philip Wadler this should be fine, so ¯\_(ツ)_/¯
-- The fine thing being that two maps that are pointwise equal are definitionally equal
-- not the idea of functional extensionality itself
-- (We just won't define insertion sort and merge sort as maps :))
postulate
  extensionality : {a b : Level} → {A : Setoid {a}} → {B : Setoid {b}} → {f g : Map A B} → (∀ (x : ∣ A ∣) → B ~ (map f x) ＝ (map g x)) → f ≡ g


test-ext : test-map ≡ test-map
test-ext = extensionality λ { x → refl } 

map-setoid : {a b : Level} → Setoid {a} → Setoid {b} → Setoid {suc a ⊔ suc b}
map-setoid A B =
    record {
        carrier = Map A B
      ; _＝_ = _≡_
      ; equivalence-relation = record { eq_refl = λ x → refl ; eq_transitive = λ { refl refl → refl } ; eq_symmetric = λ { refl → refl } }
      }

_⇒_ : {a b : Level} → (A : Setoid {a}) → (B : Setoid {b}) → Setoid {suc a ⊔ suc b}
A ⇒ B = map-setoid A B

ap2 : {A B C : Setoid} → (f : ∣ (A ⇒ (B ⇒ C)) ∣) → (a : ∣ A ∣) → (∣ B ∣ → ∣ C ∣)
ap2 {A} {B} {C} f a = Map.map (map f a) 

record Category {o l e : Level} : Set (suc (suc o ⊔ l ⊔ e)) where
  eta-equality
  open Setoid
  infix 9 _∘_
  field
    Obj : Set o
    hom : Obj → Obj → Setoid {o}
    _∘_ : {A B C : Obj} → (g : ∣ hom B C ∣) → (f : ∣ hom A B ∣) → ∣ (hom A C) ∣
    id : (A : Obj) → ∣ (hom A A) ∣
    associative : {A B C D : Obj} {f : ∣ hom A B ∣} {g : ∣ hom B C ∣} {h : ∣ hom C D ∣} → hom A D ~ ((h ∘ g) ∘ f) ＝ (h ∘ (g ∘ f))
    id-law-left : {A B : Obj} {f : ∣ hom A B ∣} → hom A B ~ ((id B) ∘ f) ＝ f
    id-law-right : {A B : Obj} {f : ∣ hom A B ∣ } → hom A B ~ (f ∘ (id A)) ＝ f



one-hom : One → One → Setoid
one-hom one one =
  record {
      carrier = one ≡ one
    ; _＝_ = λ { x y → x ≡ y }
    ; equivalence-relation = record { eq_refl = λ{ refl → refl }; eq_transitive = λ{ refl refl → refl }; eq_symmetric = λ{ refl → refl }}
    }

--The one object category with one arrow
one_cat : Category
one_cat = record
           { Obj = One
           ; hom = one-hom 
           ; _∘_ = λ{ {one} {one} {one} refl refl → refl }
           ; id = λ{ one → refl }
           ; associative = λ{ {one} {one} {one} {one} {refl} {refl} {refl} → refl }
           ; id-law-left = λ{ {one} {one} {refl} → refl }
           ; id-law-right = λ{ {one} {one} {refl} → refl }
           }
data n-type : ℕ → ℕ → Set where
  arrow-label : {n : ℕ} → n-type n n

arrow-equivalence : Equivalence n-type
arrow-equivalence = record { eq_refl = λ x → arrow-label ; eq_transitive = λ{ arrow-label arrow-label → arrow-label }; eq_symmetric = λ{ arrow-label → arrow-label }}

n-setoid : One → One → Setoid
n-setoid one one =
  record {
      carrier = ℕ
    ; _＝_ = λ{ x y → n-type x y }
    ; equivalence-relation = arrow-equivalence
    }

id-helper-left : Equivalence n-type → (f : ∣ n-setoid one one ∣) → n-setoid one one ~ f + ℕ.zero ＝ f
id-helper-left record { eq_refl = eq_refl ; eq_transitive = eq_transitive ; eq_symmetric = eq_symmetric } f = eq_transitive {! arrow-label (f + ℕ.zero)!} {!!}

integers : Category 
integers = record
            { Obj = One
            ; hom = n-setoid
            ; _∘_ = λ{ {one} {one} {one} g f → f + g }
            ; id = λ{ one → ℕ.zero }
            ; associative = {!!} 
            ; id-law-left = λ{ {one} {one} {f} → {!!} }
            ; id-law-right = λ{ {one} {one} {f} → arrow-label }
            }

