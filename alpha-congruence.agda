open import Agda.Builtin.Maybe using (just; nothing)
open import Data.List using (List; [_]; _∷_; find; []) 
open import Relation.Binary.PropositionalEquality as Eq
  hiding(subst)
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty; _⊂_; _⊆_)
open import Relation.Nullary using (_⊎-dec_)
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
open import Relation.Nullary.Negation using (contradiction)

module alpha-congruence (id : Set)
  (_≡ᵢ_ : DecidableEquality id)
  (fresh-variable : {l : Level} → (p : Pred id l) → Decidable p → Σ[ x ∈ id ] x ∉ p)
  (start-id : id) where

open import lambda-calculus id _≡ᵢ_ fresh-variable start-id

distribute : {A B C : Set} → (A ⊎ B → C) → ((A → C) × (B → C))
distribute f = (λ x → f (inj₁ x)) , λ x → f (inj₂ x)

distribute-two : {l : Level} → {A B : Set} → (P P' : Pred A l) → (a : A) → ((P ∪ P') a) → (P a → B) → (P' a → B) → B
distribute-two P P' a (inj₁ x) f g = f x

distribute-two P P' a (inj₂ y) f g = g y

convert : (m : Λ) → (x y : id) → x ≢ y → ∃[ l ] x ∉ V⟨ l ⟩
convert (` z) x y neg with z ≡ᵢ x
... | no ¬a = (` z) , (λ{ (inj₂ refl) → ¬a refl})
... | yes a = (` y) , (λ{ (inj₂ refl) → neg refl })
convert (m · n) x y neg with convert m x y neg | convert n x y neg
... | m' , e | n' , e' with distribute e | distribute e'
... | bvm , fvm | bvn , fvn = (m' · n') , λ{ (inj₁ set) → distribute-two BV⟨ m' ⟩ BV⟨ n' ⟩ x set bvm bvn
                                           ; (inj₂ set) → distribute-two FV⟨ m' ⟩ FV⟨ n' ⟩ x set fvm fvn }
convert (ƛ z ⇒ m) x y neg with z ≡ᵢ x | convert m x y neg
... | no ¬a | m' , e = (ƛ z ⇒ m') , λ{ (inj₁ (inj₁ refl)) → contradiction refl ¬a
                                      ; (inj₁ (inj₂ y)) → e (inj₁ y)
                                      ; (inj₂ (fst , snd)) → e (inj₂ fst) }
... | yes a | m' , e = (ƛ x ⇒ m') , λ{ (inj₁ (inj₁ x)) → e {!!}
                                      ; (inj₁ (inj₂ y)) → e (inj₁ y)
                                      ; (inj₂ y) → {!y!} }

non-equality : {l : Level} → {A : Set} → (P : Pred A l) → (a b : A) → (P a) → ¬ (P b) → a ≢ b
non-equality P a b prop prop' refl = prop' prop

subst : (x y : id) → (m : Λ) → Λ
subst x y (` x') with x ≡ᵢ x'
... | no _ = ` x'
... | yes _ = ` y
subst x y (m · n) = subst x y m · subst x y n
subst x y (ƛ x' ⇒ m) with x ≡ᵢ x'
... | no _ = ƛ x' ⇒ subst x y m
... | yes _ = ƛ x' ⇒ m

data _＝α_ : Λ → Λ → Set where
  α-equality : {m n : Λ} → {x y : id} → m ＝α (subst x y n) → (ƛ x ⇒ m) ＝α (ƛ y ⇒ n)

postulate equal-implies-alpha : {m n : Λ} → m ＝ n → m ＝α n

subst-lemma : (x y : id) → x ≡ y → (m : Λ) → m ＝ subst x y m
subst-lemma x y prop (` x') with x ≡ᵢ x'
... | no ¬a = reflexive
subst-lemma x y refl (` x') | yes refl = reflexive
subst-lemma x y prop (m · n) with subst-lemma x y prop m | subst-lemma x y prop n
... | prop | prop-two = transitive (application prop) (extensional prop-two)
subst-lemma x y prop (ƛ x' ⇒ m) with x ≡ᵢ x'
... | yes a = reflexive
... | no ¬a with subst-lemma x y prop m
... | prop' = rule-e x' prop'

subst-symmetric : (x y : id) → (m n : Λ) → m ＝α subst x y n → subst x y n ＝α m
subst-symmetric x y m n prop = {!!}


postulate α-congruence-imples-＝ : {m n : Λ} → m ＝α n → m ＝ n

＝α-sym : Symmetric _＝α_
＝α-sym m = equal-implies-alpha {!symmetric!}

＝α-trans : Transitive _＝α_
＝α-trans m p = {!!}

＝α-decidable : IsDecEquivalence _＝α_
＝α-decidable = record {
    isEquivalence = record { refl = {!!} ; sym = ＝α-sym ; trans = ＝α-trans }
    ; _≟_ = λ x y → {!!}
  }

name-normalize' : id → List (id × id) → Λ → Λ
name-normalize' _ ids (` x) with find (λ (old , _) → x ≡ᵢ old) ids
... | just (_ , new) = ` new
... | nothing = ` x
name-normalize' cur ids (m · n) = name-normalize' cur ids m · name-normalize' cur ids n
name-normalize' cur ids (ƛ x ⇒ l) = 
  let new-term = (ƛ cur ⇒ l)
  in
  ƛ cur ⇒ name-normalize' (proj₁ (fresh-variable FV⟨ new-term ⟩ λ x' → _FV>_ new-term x')) ((x , cur) ∷ ids) l 

name-normalize : id → Λ → Λ
name-normalize x (` x') = ` x'
name-normalize x (m · m') = name-normalize x m · name-normalize x m'
name-normalize x (ƛ x' ⇒ m) = ƛ x ⇒ (name-normalize' x (Data.List.[ (x' , x) ]) m)

name-normalize-idempotent : (m : Λ) → name-normalize start-id m ＝ name-normalize start-id (name-normalize start-id m)
name-normalize-idempotent (` x) = reflexive
name-normalize-idempotent (m · n) with name-normalize-idempotent m | name-normalize-idempotent n
... | prop | prop-two =  transitive (extensional prop-two) (application prop)
name-normalize-idempotent (ƛ x ⇒ m) with name-normalize-idempotent m 
... | prop = {!!}
  where
  helper : (m : Λ) → name-normalize' start-id ((start-id , start-id) ∷ []) m ＝ m
  helper (` x) with x ≡ᵢ start-id
  ... | no ¬a = reflexive
  ... | yes refl = reflexive
  helper (m · n) = transitive (application (helper m)) (extensional (helper n))
  helper (ƛ x' ⇒ m) with x' ≡ᵢ start-id
  ... | no ¬a = {!!}
  ... | yes a = {!!}



--rule-e start-id (transitive identity
--                                 (symmetric
--                                  (helper (name-normalize' start-id ((x , start-id) ∷ []) m))))


-- α-conversion takes a term and a variable to replace and gives back
-- the new term, the new id generated to replace the old term
-- and evidence that the old term is no longer in the variables of the new term
α-conversion : (m : Λ) → (x : id) → ∃[ l ] (m ＝α l) × ∃[ y ] x ∉ V⟨ l ⟩
α-conversion m x = 
    -- We apply our term to x so that x is a variable in our original lambda term
    -- This way we get a totally new variable and don't need evidence that
    -- the x to be replaced is in the free of m
    -- If this happens then nothing about m should change and we should just
    -- get evidence that our original variable wasn't in x
    -- along with an extra unused variable that we could get rid of
    let  x' , fv = fresh-variable (V⟨ m · (` x) ⟩) λ{ x' → _V>_ (m · ` x) x' }
         l , prop = convert m x x' (non-equality V⟨ m · ` x ⟩ x x' (inj₂ (inj₂ refl)) fv)
    in
      l , {!!} , x' , prop

