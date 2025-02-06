open import Data.String using (String; _==_; _≟_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec; ×-≡,≡↔≡)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty; _⊂_; _⊆_)
open import Level using (Level; 0ℓ)
open import Data.Sum
open import Function using (_∘_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)
open import Data.Nat.Properties as N
open import Relation.Binary using (Rel; DecidableEquality; IsDecEquivalence; Transitive; Symmetric)
open import Relation.Nullary using (_⊎-dec_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List using (List; [_]; _∷_; find; []) 

module lambda-calculus (id : Set)
  (_≡ᵢ_ : DecidableEquality id)
  (fresh-variable : {l : Level} → (p : Pred id l) → Decidable p → Σ[ x ∈ id ] x ∉ p)
  (start-id : id) where

  private
    variable
      a b c ℓ ℓ₁ ℓ₂ : Level
      A : Set a
      B : Set b
    infix 0 _≃_
    record _≃_ (A B : Set) : Set where
      field
        to   : A → B
        from : B → A
        from∘to : ∀ (x : A) → from (to x) ≡ x
        to∘from : ∀ (y : B) → to (from y) ≡ y
  open _≃_

  _-_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P - Q = λ x → x ∈ P × x ∉ Q

  data Λ : Set where
    `_ : id → Λ
    _·_ : Λ → Λ → Λ
    ƛ_⇒_ : id → Λ → Λ
  
  infix  5  ƛ_⇒_
  infixl 7  _·_
  infix  9  `_
  
  infix 9 _[_:=_]
  
  FV⟨_⟩ : Λ → Pred id _
  FV⟨ ` x ⟩ = ｛ x ｝
  FV⟨ term · term₁ ⟩ = FV⟨ term ⟩ ∪ FV⟨ term₁ ⟩
  FV⟨ ƛ x ⇒ term ⟩ = FV⟨ term ⟩ - ｛ x ｝

  BV⟨_⟩ : Λ → Pred id _
  BV⟨ ` x ⟩ = ∅
  BV⟨ x · y ⟩ = BV⟨ x ⟩ ∪ BV⟨ y ⟩
  BV⟨ ƛ x ⇒ y ⟩ = ｛ x ｝ ∪ BV⟨ y ⟩

  V⟨_⟩ : Λ → Pred id _ 
  V⟨ x ⟩ = BV⟨ x ⟩ ∪ FV⟨ x ⟩

  private
    symmetry : {x y : id} → x ≡ y → y ≡ x
    symmetry refl = refl


  _BV>_ : (l : Λ) → Decidable BV⟨ l ⟩
  _BV>_ (` x) id = no (λ{ () })
  _BV>_ (x · y) id with (_BV>_ x) id | (_BV>_ y) id
  ... | prop | prop-two = prop ⊎-dec prop-two
  _BV>_ (ƛ x ⇒ y) id with id ≡ᵢ x
  ... | yes a = yes (inj₁ (symmetry a))
  ... | no ¬a with y BV> id
  ... | no ¬a' = no λ{ (inj₁ x) → ¬a (symmetry x) ; (inj₂ y) → ¬a' y }
  ... | yes a' = yes (inj₂ a')

  _FV>_ : (l : Λ) → Decidable FV⟨ l ⟩
  _FV>_ (` x₁) x with x₁ ≡ᵢ x
  ... | no ¬p = no ¬p
  ... | yes p = yes p
  _FV>_ (l · l₁) x with (_FV>_ l) x | (_FV>_ l₁) x
  ... | dec | dec₁ = dec ⊎-dec dec₁
  _FV>_ (ƛ x₁ ⇒ l₁) x with x₁ ≡ᵢ x
  ... | yes p₁ = no λ { pred → proj₂ pred p₁ }
  ... | no ¬p with l₁ FV> x
  ... | no ¬p₁ = no λ pair → ¬p₁ (proj₁ pair)
  ... | yes p = yes (p , ¬p)
  
  _V>_ : (l : Λ) → Decidable V⟨ l ⟩  
  x V> id with V⟨ x ⟩ | x FV> id | x BV> id
  ... | vs | no ¬a | no ¬b = no λ{ (inj₁ x) → ¬b x ; (inj₂ y) → ¬a y }
  ... | vs | no ¬a | yes a = yes (inj₁ a)
  ... | vs | yes a | bv = yes (inj₂ a)

  {-# TERMINATING #-}
  _[_:=_]α : Λ → id → Λ → Λ 
  (` x) [ y := M ]α with x ≡ᵢ y
  ... | yes _         = M
  ... | no  _         = ` x
  (L · M) [ y := V ]α  = (L [ y := V ]α) · (M [ y := V ]α)
  (ƛ x ⇒ N) [ y := M ]α with x ≡ᵢ y
  ... | yes _         = ƛ x ⇒ N
  ... | no _ with _FV>_ N y | _FV>_ M x
  ... | yes p | yes p₁ =
    let temp = proj₁ (fresh-variable FV⟨ N ⟩ λ{ x' → _FV>_ N x' })
        Mtemp = M · (` temp)
        z = proj₁ (fresh-variable FV⟨ Mtemp ⟩ λ{ x' → _FV>_ Mtemp x' })
    in
    (ƛ z ⇒ M) [ y := ` x ]α [ x := N ]α
  ... | _ | _ = (ƛ y ⇒ M) [ y := ` y ]α [ x := N ]α

  _[_:=_] : Λ → id → Λ → Λ 
  (` x) [ y := M ] with x ≡ᵢ y
  ... | yes _         = M
  ... | no  _         = ` x
  (L · M) [ y := V ]  = (L [ y := V ]) · (M [ y := V ])
  (ƛ x ⇒ N) [ y := M ] with x ≡ᵢ y
  ... | yes _         = ƛ x ⇒ N
  ... | no _          = ƛ x ⇒ (N [ y := M ])
  
  
  data _＝_ : Λ → Λ → Set where
    β-conversion : ( x : id ) → (m n : Λ) → ((ƛ x ⇒ m) · n) ＝ (m [ x := n ])
    reflexive : {x : Λ} → x ＝ x
    symmetric : {x y : Λ} → x ＝ y → y ＝ x
    transitive : {x y z : Λ} → x ＝ y → y ＝ z → x ＝ z
    application : {m n z : Λ} → m ＝ n → (m · z) ＝ (n · z)
    extensional : {m n z : Λ} → m ＝ n → (z · m) ＝ (z · n)
    rule-e : {m n : Λ} → (x : id) → m ＝ n → (ƛ x ⇒ m) ＝ (ƛ x ⇒ n)

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
    x ∎  = reflexive
  
  Sub⟨_⟩ : Λ → Pred Λ _
  Sub⟨ ` x ⟩ = ｛ ` x ｝
  Sub⟨ x · x₁ ⟩ = Sub⟨ x ⟩ ∪ Sub⟨ x₁ ⟩ ∪ ｛ x · x₁ ｝
  Sub⟨ ƛ x ⇒ x₁ ⟩ = Sub⟨ x₁ ⟩ ∪ ｛ ƛ x ⇒ x₁ ｝
  
  record Λ⁰ : Set where
    field
      term : Λ
      closed : Empty FV⟨ term ⟩
  
--  data Subterm : Set where
--    _⊂_ : (M N : Λ) → M ∈ Sub⟨ N ⟩ → Subterm
  
  definitional-equivalence : {x y : Λ} → x ≡ y → x ＝ y
  definitional-equivalence refl = reflexive
  
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
  
  free-variable-substitution : (f g : Λ) → (x : id) → x ∉ FV⟨ f ⟩ → (f [ x := g ]) ＝ f
  free-variable-substitution (` x₁) g x x∉f with x₁ ≡ᵢ x
  ... | no ¬p = reflexive
  ... | yes p with x∉f p
  ... | ()
  free-variable-substitution (f · f₁) g x x∉f with free-variable-substitution f g x | free-variable-substitution f₁ g x
  ... | ans | ans1 with ⊎→× x∉f
  ... | fst , snd with ans1 snd | ans fst
  ... | resp1 | resp2 = lemma resp2 resp1
  free-variable-substitution (ƛ x₁ ⇒ f) g x x∉f with x₁ ≡ᵢ x
  ... | yes p = reflexive
  ... | no ¬p with f FV> x 
  ... | yes p₁ = contradiction (p₁ , ¬p)  x∉f
  ... | no p with free-variable-substitution f g x p
  ... | prop = rule-e x₁ prop
  
  fixed-point-theorem : ∀ (f : Λ) → ∃[ x ] (f · x) ＝ x
  fixed-point-theorem f = X ,
    symmetric (begin
      X
    ＝⟨⟩
      W · W
    ＝⟨⟩
      (ƛ idn ⇒ fun) · W
    ＝⟨ β-conversion idn fun W ⟩
      fun [ idn := W ]
    ＝⟨ helper ⟩
      (f · (W · W))
    ＝⟨⟩
      f · (X)
    ∎)
    where
      new-term : Σ[ i ∈ id ] (i ∉ FV⟨ f ⟩)
      new-term = fresh-variable FV⟨ f ⟩ λ x → f FV> x 
      idn = proj₁ new-term
      proof = proj₂ new-term
      fun = f · ((` idn) · (` idn))
      W = ƛ idn ⇒ fun
      X = W · W
      helper-two : (g : Λ) → ((` idn) [ idn := g ]) ＝ g
      helper-two g with idn ≡ᵢ idn
      ... |  no ¬p = contradiction refl ¬p
      ... |  yes p = reflexive
      helper-three : (((` idn) [ idn := W ]) · ((` idn) [ idn := W ])) ＝ (W · W)
      helper-three = lemma (helper-two W) (helper-two W)
      helper : (fun [ idn := W ]) ＝ (f · (W · W))
      helper = begin
               (f [ idn := W ]) · (((` idn) [ idn := W ]) ·
               ((` idn) [ idn := W ]))
             ＝⟨ extensional helper-three ⟩
               (f [ idn := W ]) · (W · W)
             ＝⟨ application (free-variable-substitution f W idn proof) ⟩
               f · (W · W) 
             ∎
  
  
  ƛ→_⇒_ : List id → Λ → Λ
  ƛ→ [] ⇒ term = term
  ƛ→ (x ∷ ids) ⇒ term = ƛ x ⇒ (ƛ→ ids ⇒ term)
  
  data Theory {l : Level} : Set (Level.suc l) where
    theory : (terms : Set) → (axioms : Rel terms l) → Theory {l}
  
  data equation {l : Level} (t : Theory {l}) (M N : Λ) : Set (Level.suc l) where
    formula : equation t M N

