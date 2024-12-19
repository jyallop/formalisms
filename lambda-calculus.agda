open import Data.String using (String; _==_; _≟_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec; ×-≡,≡↔≡)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Level using (Level; 0ℓ)
open import Data.Sum
open import Function using (_∘_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)
open import Data.Nat.Properties as N
open import Relation.Binary using (Rel; DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary using (_⊎-dec_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b


_-_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P - Q = λ x → x ∈ P × x ∉ Q

Id = String × ℕ

data Λ : Set where
  `_ : Id → Λ
  _·_ : Λ → Λ → Λ
  ƛ_⇒_ : Id → Λ → Λ

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_

_≡ⁱ_ : DecidableEquality Id
_≡ⁱ_ = ≡-dec Data.String._≟_ N._≟_

infix 9 _[_:=_]

FV⟨_⟩ : Λ → Pred Id _
FV⟨ ` x ⟩ = ｛ x ｝
FV⟨ term · term₁ ⟩ = FV⟨ term ⟩ ∪ FV⟨ term₁ ⟩
FV⟨ ƛ x ⇒ term ⟩ = FV⟨ term ⟩ - ｛ x ｝

_FV>_ : (l : Λ) → Decidable FV⟨ l ⟩
_FV>_ (` x₁) x with x₁ ≡ⁱ x
... | no ¬p = no ¬p
... | yes p = yes p
_FV>_ (l · l₁) x with (_FV>_ l) x | (_FV>_ l₁) x
... | dec | dec₁ = dec ⊎-dec dec₁
_FV>_ (ƛ x₁ ⇒ l₁) x with x₁ ≡ⁱ x
...
  |
  yes p₁ =
   no λ { pred → proj₂ pred p₁ }
... | no ¬p with l₁ FV> x
... | no ¬p₁ = no λ pair → ¬p₁ (proj₁ pair)
... | yes p = yes (p , ¬p)

{-# TERMINATING #-}
new-free-identifier : Id → (l : Λ) → Σ[ x ∈ Id ] x ∉ FV⟨ l ⟩
new-free-identifier id@(term , incr) set with (_FV>_ set) id 
... | no ¬p = (term , incr) , ¬p
... | yes p = new-free-identifier (term , suc incr) set

-- {-# TERMINATING #-}
-- _[_:=_] : Λ → Id → Λ → Λ 
-- (` x) [ y := M ] with x ≡ⁱ y
-- ... | yes _         = M
-- ... | no  _         = ` x
-- (L · M) [ y := V ]  = (L [ y := V ]) · (M [ y := V ])
-- (ƛ x ⇒ N) [ y := M ] with x ≡ⁱ y
-- ... | yes _         = ƛ x ⇒ N
-- ... | no _ with _FV>_ N y | _FV>_ M x
-- ... | no ¬p | no ¬p₁ = ((ƛ "z" , 0 ⇒ M) [ y := ` ("z" , 0) ]) [ x := N ]
-- ... | no ¬p | yes p = ((ƛ "z" , 0 ⇒ M) [ y := ` ("z" , 0) ]) [ x := N ]
-- ... | yes p | no ¬p = ((ƛ "z" , 0 ⇒ M) [ y := ` ("z" , 0) ]) [ x := N ]
-- ... | yes p | yes p₁ = let z = proj₁ (new-free-identifier (proj₁ (new-free-identifier y N)) M)
--                              in
--                              (ƛ z ⇒ M) [ y := ` x ] [ x := N ]
 

_[_:=_] : Λ → Id → Λ → Λ 
(` x) [ y := M ] with x ≡ⁱ y
... | yes _         = M
... | no  _         = ` x
(L · M) [ y := V ]  = (L [ y := V ]) · (M [ y := V ])
(ƛ x ⇒ N) [ y := M ] with x ≡ⁱ y
... | yes _         = ƛ x ⇒ N
... | no _          = ƛ x ⇒ (N [ y := M ])


data _＝_ : Λ → Λ → Set where
  β-conversion : ( x : Id ) → (m n : Λ) → ((ƛ x ⇒ m) · n) ＝ (m [ x := n ])
  identity : {x : Λ} → x ＝ x
  reflexive : {x y : Λ} → x ＝ y → y ＝ x
  transitive : {x y z : Λ} → x ＝ y → y ＝ z → x ＝ z
  application : {m n z : Λ} → m ＝ n → (m · z) ＝ (n · z)
  extensional : {m n z : Λ} → m ＝ n → (z · m) ＝ (z · n)
  rule-e : {m n : Λ} → (x : Id) → m ＝ n → (ƛ x ⇒ m) ＝ (ƛ x ⇒ n)

module ＝-Reasoning where

  infix  1 begin_
  infixr 2 _＝⟨⟩_ _＝⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : Λ}
    → x ＝ y
      -----
    → x ＝ y
  begin x≡y  =  x≡y

  _＝⟨⟩_ : ∀ (x : Λ) {y : Λ}
    → x ＝ y
      -----
    → x ＝ y
  x ＝⟨⟩ x＝y  =  x＝y

  _＝⟨_⟩_ : ∀ (x : Λ) {y z : Λ}
    → x ＝ y
    → y ＝ z
      -----
    → x ＝ z
  x ＝⟨ x＝y ⟩ y＝z  =  transitive x＝y y＝z

  _∎ : ∀ (x : Λ)
      -----
    → x ＝ x
  x ∎  = identity

Sub⟨_⟩ : Λ → Pred Λ _
Sub⟨ ` x ⟩ = ｛ ` x ｝
Sub⟨ x · x₁ ⟩ = Sub⟨ x ⟩ ∪ Sub⟨ x₁ ⟩ ∪ ｛ x · x₁ ｝
Sub⟨ ƛ x ⇒ x₁ ⟩ = Sub⟨ x₁ ⟩ ∪ ｛ ƛ x ⇒ x₁ ｝

data Subterm : Set where
  _⊂_ : (M N : Λ) → M ∈ Sub⟨ N ⟩ → Subterm

data ActiveSubterm : Set where
--  _⊂_ : (M N : Λ) → M ∈ Sub⟨ N ⟩ → ∃[ Z ] ((N · Z) ⊂ M) → ActiveSubterm

syntactic-equivalence : {x y : Λ} → x ≡ y → x ＝ y
syntactic-equivalence refl = identity

⊎→× : ∀ {A B C : Set} → (A ⊎ B → C) → ((A → C) × (B → C))
⊎→× = λ{ f → f ∘ inj₁ , f ∘ inj₂ }

open ＝-Reasoning

lemma :
  {f g h i : Λ} → f ＝ g → h ＝ i → (f · h) ＝ (g · i)
lemma {f} {g} {h} {i} f＝g h＝i = begin
                 f · h
      ＝⟨ extensional h＝i ⟩
      f · i
      ＝⟨ application f＝g ⟩
      g · i
  ∎

free-variable-substitution : (f g : Λ) → (x : Id) → x ∉ FV⟨ f ⟩ → (f [ x := g ]) ＝ f
free-variable-substitution (` x₁) g x x∉f with x₁ ≡ⁱ x
... | no ¬p = identity
... | yes p with x∉f p
... | ()
free-variable-substitution (f · f₁) g x x∉f with free-variable-substitution f g x | free-variable-substitution f₁ g x
... | ans | ans1 with ⊎→× x∉f
... | fst , snd with ans1 snd | ans fst
... | resp1 | resp2 = lemma resp2 resp1
free-variable-substitution (ƛ x₁ ⇒ f) g x x∉f with x₁ ≡ⁱ x
... | yes p = identity
... | no ¬p with f FV> x 
... | yes p₁ = contradiction (p₁ , ¬p)  x∉f
... | no p with free-variable-substitution f g x p
... | prop = rule-e x₁ prop

fixed-point-theorem : ∀ (f : Λ) → ∃[ x ] x ＝ (f · x) 
fixed-point-theorem f = X ,
  (begin
    X
  ＝⟨⟩
    W · W
  ＝⟨⟩
    (ƛ id ⇒ fun) · W
  ＝⟨ β-conversion id fun W ⟩
    fun [ id := W ]
  ＝⟨ helper ⟩
    (f · (W · W))
  ＝⟨⟩
    f · (X)
  ∎)
  where
    new-term : Σ[ id ∈ Id ] (id ∉ FV⟨ f ⟩)
    new-term = new-free-identifier ("x" , 0) f
    id = proj₁ new-term
    proof = proj₂ new-term
    fun = f · ((` id) · (` id))
    W = ƛ id ⇒ fun
    X = W · W
    helper-two : (g : Λ) → ((` id) [ id := g ]) ＝ g
    helper-two g with id ≡ⁱ id
    ... |  no ¬p = contradiction refl ¬p
    ... |  yes p = identity
    helper-three : (((` id) [ id := W ]) · ((` id) [ id := W ])) ＝ (W · W)
    helper-three = lemma (helper-two W) (helper-two W)
    helper : (fun [ id := W ]) ＝ (f · (W · W))
    helper = begin
             (f [ id := W ]) · (((` id) [ id := W ]) ·
             ((` id) [ id := W ]))
           ＝⟨ extensional helper-three ⟩
             (f [ id := W ]) · (W · W)
           ＝⟨ application (free-variable-substitution f W id proof) ⟩
             f · (W · W) 
           ∎


ƛ→_⇒_ : List Id → Λ → Λ
ƛ→ [] ⇒ term = term
ƛ→ x ∷ ids ⇒ term = ƛ x ⇒ (ƛ→ ids ⇒ term)

data Con (M N : Λ) : Set where
  consistent : (prop : M ＝ N) → ∀(A B : Λ) → ¬ (A ＝ B) → Con M N

data Theory {l : Level} : Set (Level.suc l) where
  theory : (terms : Set) → (axioms : Rel terms l) → Theory {l}

data equation {l : Level} (t : Theory {l}) (M N : Λ) : Set (Level.suc l) where
  formula : equation t M N

