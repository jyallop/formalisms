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
open import Level using (Level; 0ℓ; suc)
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

open import lambda-calculus id _≡ᵢ_ fresh-variable start-id -- using (Λ; `_; _·_; ƛ_⇒_; V⟨_⟩; BV⟨_⟩; FV⟨_⟩; _＝_)

non-equality : {l : Level} → {A : Set} → (P : Pred A l) → (a b : A) → (P a) → ¬ (P b) → a ≢ b
non-equality P a b prop prop' refl = prop' prop

subst : (new old : id) → Λ → Λ
subst new old (` x) with x ≡ᵢ old
... | no ¬a = ` x
... | yes a = ` new
subst new old (m · n) = subst new old m · subst new old n
subst new old (ƛ x ⇒ m) with x ≡ᵢ old
... | no ¬a = ƛ x ⇒ subst new old m
... | yes a = ƛ new ⇒ subst new old m

subst-idem : (new old : id) → (new ≢ old) → (m : Λ) → old ∉ V⟨ (subst new old m) ⟩
subst-idem new old prop (` x) with x ≡ᵢ old
... | no ¬a = λ{ (inj₂ refl) → ¬a refl }
... | yes a = λ{ (inj₂ refl) → prop refl }
subst-idem new old prop (m · n) with subst-idem new old prop m | subst-idem new old prop n
... | e | e' = λ{ (inj₁ (inj₁ x)) → e (inj₁ x)
                ; (inj₁ (inj₂ y)) → e' (inj₁ y)
                ; (inj₂ (inj₁ x)) → e (inj₂ x)
                ; (inj₂ (inj₂ y)) → e' (inj₂ y) }
subst-idem new old prop (ƛ x ⇒ m) with x ≡ᵢ old | subst-idem new old prop m
... | no ¬a | e = λ{ (inj₁ (inj₁ refl)) → ¬a refl
                   ; (inj₁ (inj₂ y)) → e (inj₁ y)
                   ; (inj₂ (fst , snd)) → e (inj₂ fst) }
... | yes refl | e = λ{ (inj₁ (inj₁ refl)) → prop refl
                      ; (inj₁ (inj₂ y)) → e (inj₁ y)
                      ; (inj₂ (fst , snd)) → e (inj₂ fst) }

subst-ident : (x : id) → (m : Λ) → m ＝ subst x x m
subst-ident id (` x) with x ≡ᵢ id
... | yes refl = reflexive
... | no ¬a = reflexive 
subst-ident id (m · n) with subst-ident id m | subst-ident id n
... | e | e' = transitive (application e) (extensional e')
subst-ident id (ƛ x ⇒ m) with x ≡ᵢ id | subst-ident id m
... | no ¬a | e' = rule-e x e'
... | yes refl | e' = rule-e x e'

subst-free : (new old : id) → (m : Λ) → old ∉ V⟨ m ⟩ → m ＝ (subst new old m)
subst-free new old (` x) prop with x ≡ᵢ old
... | no ¬a = reflexive
... | yes refl = contradiction (refl {0ℓ} {id} {old}) (λ{ refl → prop (inj₂ refl) }) 
subst-free new old (m · n) prop with subst-free new old m (x∉v⟨m·n⟩→x∉v⟨m⟩ old m n prop) | subst-free new old n (x∉v⟨m·n⟩→x∉v⟨n⟩ old m n prop)
... | prop-m | prop-n = transitive (extensional prop-n) (application prop-m)
subst-free new old (ƛ x ⇒ m) prop with x ≡ᵢ old |  subst-free new old m (x∉v⟨y→m⟩→x∉v⟨m⟩ old x m prop)
... | no ¬a | prop-m = rule-e x prop-m
... | yes refl | prop-m = contradiction (refl {0ℓ} {id} {old}) (λ{ refl → prop (inj₁ (inj₁ refl)) })

subst-inver : (x y : id) → (m : Λ) → y ∉ V⟨ m ⟩ → m ＝ subst x y (subst y x m)
subst-inver x y (` x') prop with x' ≡ᵢ x 
... | no ¬a = subst-free x y (` x') λ{ (inj₂ refl) →  prop (inj₂ refl) }
... | yes refl with y ≡ᵢ y
... | no ¬b = contradiction (refl) ¬b
... | yes b = reflexive
subst-inver x y (m · n) prop with subst-inver x y m (x∉v⟨m·n⟩→x∉v⟨m⟩ y m n prop) | subst-inver x y n (x∉v⟨m·n⟩→x∉v⟨n⟩ y m n prop)
... | e | e' = transitive (application e) (extensional e')
subst-inver x y (ƛ x' ⇒ m) prop with x' ≡ᵢ x | subst-inver x y m (x∉v⟨y→m⟩→x∉v⟨m⟩ y x' m prop) 
... | no ¬a | e' with x' ≡ᵢ y
... | no ¬a₁ = rule-e x' e'
... | yes a = contradiction {_} (refl {0ℓ} {id} {x'}) (λ{ refl → prop (inj₁ (inj₁ a)) })
subst-inver x y (ƛ x' ⇒ m) prop | yes refl | e' with y ≡ᵢ y
... | no ¬b = contradiction refl ¬b
... | yes b = rule-e x e'

data _＝α_ : Λ → Λ → Set where
  α-equality-term : {x y : id} → (` x) ＝α (` y)
  α-equality-ext : {m n : Λ} → {x y : id} → m ＝ subst x y n → (ƛ x ⇒ m) ＝α (ƛ y ⇒ n)

postulate α-congruence-implies-＝ : {m n : Λ} → m ＝α n → m ＝ n

subst-lemma : (new old : id) → (m : Λ) → (new ∉ V⟨ m ⟩) → m ＝ subst new old m
subst-lemma new old (` x) prop  with x ≡ᵢ old
... | no ¬a = reflexive
... | yes refl with new ≡ᵢ old
... | no ¬a = α-congruence-implies-＝ α-equality-term 
... | yes refl = reflexive 
subst-lemma new old (m · n) prop with subst-lemma new old m (x∉v⟨m·n⟩→x∉v⟨m⟩ new m n prop) | subst-lemma new old n (x∉v⟨m·n⟩→x∉v⟨n⟩ new m n prop) 
... | prop' | prop-two = transitive (application prop') (extensional prop-two)
subst-lemma new old (ƛ x ⇒ m) prop with x ≡ᵢ old | subst-lemma new old m (x∉v⟨y→m⟩→x∉v⟨m⟩ new x m prop)
... | yes refl | e = α-congruence-implies-＝ (α-equality-ext (subst-inver old new m (x∉v⟨y→m⟩→x∉v⟨m⟩ new old m prop)))
... | no ¬a | e' = rule-e x e'

--＝α-sym : Symmetric _＝α_
--＝α-sym α-equality-term = α-equality-term
--＝α-sym (α-equality-ext x) = {!x!}

--＝α-trans : Transitive _＝α_
--＝α-trans m p = {!!}

--＝α-decidable : IsDecEquivalence _＝α_
--＝α-decidable = record {
--    isEquivalence = record { refl = {!!} ; sym = ＝α-sym ; trans = ＝α-trans }
--    ; _≟_ = λ x y → {!!}
--  }

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

--name-normalize-idempotent : (m : Λ) → name-normalize start-id m ＝ name-normalize start-id (name-normalize start-id m)
--name-normalize-idempotent (` x) = reflexive
--name-normalize-idempotent (m · n) with name-normalize-idempotent m | name-normalize-idempotent n
--... | prop | prop-two =  transitive (extensional prop-two) (application prop)
--name-normalize-idempotent (ƛ x ⇒ m) with name-normalize-idempotent m 
--... | prop = {!!}
--  where
--  helper : (m : Λ) → name-normalize' start-id ((start-id , start-id) ∷ []) m ＝ m
--  helper (` x) with x ≡ᵢ start-id
--  ... | no ¬a = reflexive
--  ... | yes refl = reflexive
--  helper (m · n) = transitive (application (helper m)) (extensional (helper n))
--  helper (ƛ x' ⇒ m) with x' ≡ᵢ start-id
--  ... | no ¬a = {!!}
--  ... | yes a = {!!}


-- α-conversion takes a term and a variable to replace and gives back
-- the new term, the new id generated to replace the old term
-- and evidence that the old term is no longer in the variables of the new term
--α-conversion : (m : Λ) → (x : id) → ∃[ l ] (m ＝α l) × ∃[ y ] x ∉ V⟨ l ⟩
--α-conversion m x = 
    -- We apply our term to x so that x is a variable in our original lambda term
    -- This way we get a totally new variable and don't need evidence that
    -- the x to be replaced is in the free of m
    -- If this happens then nothing about m should change and we should just
    -- get evidence that our original variable wasn't in x
    -- along with an extra unused variable that we could get rid of
--    let  x' , fv = fresh-variable (V⟨ m · (` x) ⟩) λ{ x' → _V>_ (m · ` x) x' }
--         l = subst x x' m --(non-equality V⟨ m · ` x ⟩ x x' (inj₂ (inj₂ refl)) fv) m
--    in
--      l , {!!} , x' , {!!}

