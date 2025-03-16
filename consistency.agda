open import identifiers
open import alpha-congruence
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty; _⊂_; _⊆_)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as Eq
  hiding(subst)
open import Data.Sum
open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)

-- In this file we take the opinion that one should not do something that would
-- take a few lines with pen and paper when one could take hundreds of lines to do
-- it instead
-- It shows that a number of different equations would be inconsistent if the
-- lambda calculus was extended with them
-- namely:
-- I ♯ K, I ♯ S, and (x y : Λ) → xx ♯ xy are all proved below
-- These are all exercises from The Lambda Calculus, its Syntax and Semantics by Henk Barendregt
-- These proofs are so long in part because we seek to deal with all the details
-- the detail that is the most pain is the need to generate combinator variables that are not free
-- in our lambda calculus
-- It would probably be much easier to define our combinators in a different way but alas tis too
-- late now :)

record _♯_ (m n : Λ) : Set₁ where
  field
    inconsistent : m ＝ n → ((A B : Λ) → A ＝ B)

-- We define our own versions of the combinators here 
-- They will be used to test our definition of inconsistency and prove the following:
m : ℕ
m = 0

n : ℕ
n = 1

o : ℕ
o = 2


-- We define our own versions of the combinators here because I don't feel like dealing with
-- the additional closed term stuff I defined in the combinators module
-- They will be used to test our definition of inconsistency
I : Λ
I = ƛ m ⇒ (` m)

K : Λ
K = ƛ m ⇒ (ƛ n ⇒ (` m))

S : Λ
S = ƛ m ⇒ (ƛ o ⇒ (ƛ n ⇒ (` m · ` n · (` o · ` n)))) 

open ＝-Reasoning

I-simplifies : {A : Λ} → (I · A) ＝ A
I-simplifies {A} =
  begin
    I · A
  ＝⟨ β-conversion m (` m) A ⟩ 
    A
  ∎

  --The ultimate goal is to prove I = K is inconsistent as an axiom
-- we start by proving I = K ­> I = A to A is any lambda term
k=i->i=A : {A : Λ} → I ＝ K → I ＝ A
k=i->i=A {A} prop =
  begin
    I
  ＝⟨ symmetric k-x-y=x ⟩
    K · x · y
  ＝⟨ symmetric (application i-x=k-x) ⟩
    I · x · y
  ＝⟨ i-x-y=x-y ⟩
    x · y
  ＝⟨ x-y=a ⟩
    A
  ∎
    where
    x : Λ
    x = I
    y : Λ
    y = A
    k-x-y=x : (K · x · y) ＝ x
    k-x-y=x =
      begin
        K · x · y
      ＝⟨ reflexive ⟩
        (ƛ m ⇒ ƛ n ⇒ ` m) · x · y
      ＝⟨ application (β-conversion m (ƛ n ⇒ ` m) x) ⟩
        (ƛ n ⇒ x) · y
      ＝⟨ β-conversion n x y ⟩
        x
      ∎
    i-x=k-x : (I · x) ＝ (K · x)
    i-x=k-x = application prop
    i-x-y=x-y : (I · x · y) ＝ (x · y)
    i-x-y=x-y = 
      begin
        I · x · y
      ＝⟨ reflexive ⟩
        ((ƛ m ⇒ ` m) · x) · y
      ＝⟨ application (β-conversion m (` m) x) ⟩
         ((` m) [ m := x ]) · y
      ＝⟨ reflexive ⟩
        x · y
      ∎
    x-y=a : (x · y) ＝ A
    x-y=a =
      begin
        x · y
      ＝⟨ reflexive ⟩
        x · A
      ＝⟨ β-conversion m (` m) A ⟩
        A
      ∎

-- We finish the goal proposition through two applications of the above proof
k=i-inconsistent : {A B : Λ} → I ＝ K → A ＝ B
k=i-inconsistent {A} {B} prop =
  begin
    A
  ＝⟨ symmetric (k=i->i=A prop) ⟩
    I
  ＝⟨ k=i->i=A prop ⟩ 
    B
  ∎

-- We can finally say that I = K is in fact inconsistent
I♯K : I ♯ K
I♯K = record {
  inconsistent = λ x A B → k=i-inconsistent x
  }

s=i->A=B : {A B : Λ}  → I ＝ S → A ＝ B
s=i->A=B {A} {B} prop =
  begin
    A
  ＝⟨ symmetric lemma-one ⟩
    I · K · A · B
  ＝⟨ application (application (application prop)) ⟩
    S · K · A · B
  ＝⟨ lemma-two ⟩ 
    K · B · (A · B)
  ＝⟨ application (extensional B＝B') ⟩
    K · B' · (A · B)
  ＝⟨ reflexive ⟩
    (ƛ m ⇒ (ƛ n ⇒ ` m)) · B' · (A · B)
  ＝⟨ application (β-conversion m (ƛ n ⇒ ` m) B') ⟩
    (ƛ n ⇒ B') · (A · B) 
  ＝⟨ β-conversion n B' (A · B) ⟩ 
    B' [ n := (A · B) ]
  ＝⟨ free-variable-substitution B' (A · B) n (x∉v→x∉fv n B' n∉VB') ⟩
    B'
  ＝⟨ symmetric B＝B' ⟩
    B
  ∎
  where
  fresh-id-A : Σ[ x ∈ ℕ ] x ∉ V⟨ A · (` n) ⟩
  fresh-id-A = new-identifier 0 (V⟨ A · (` n) ⟩) λ x → (A · (` n)) V> x
  id-A : ℕ
  id-A = proj₁ fresh-id-A
  new-var-A : id-A ∉ V⟨ A · (` n) ⟩
  new-var-A = proj₂ fresh-id-A
  ida∉A : id-A ∉ V⟨ A ⟩
  ida∉A = x∉v⟨m·n⟩→x∉v⟨m⟩ id-A A (` n) new-var-A
  ida≢n : n ≢ id-A
  ida≢n = non-equality ℕ _≡ᵢ_ (new-identifier 0) 0 V⟨ A · ` n ⟩ n id-A (inj₂ (inj₂ refl))
    λ{ (inj₁ (inj₁ x)) → ida∉A (inj₁ x)
     ; (inj₂ (inj₁ x)) → ida∉A (inj₂ x)
     ; (inj₂ (inj₂ y)) → x∉v⟨m·n⟩→x∉v⟨n⟩ id-A A (` n) new-var-A (inj₂ y) }
  A' : Λ
  A' = subst ℕ _≡ᵢ_ (new-identifier 0) 0 (proj₁ fresh-id-A) n A
  A＝A' : A ＝ A'
  A＝A' = subst-lemma ℕ _≡ᵢ_ (new-identifier 0) 0 id-A n A ida∉A
  n∉VA' : n ∉ V⟨ A' ⟩
  n∉VA' = subst-idem ℕ _≡ᵢ_ (new-identifier 0) 0 id-A n (λ{ x → ida≢n (sym x) }) A
  fresh-id-B : Σ[ x ∈ ℕ ] x ∉ V⟨ B · (` n) ⟩
  fresh-id-B = new-identifier 0 (V⟨ B · (` n) ⟩) λ x → (B · (` n)) V> x
  id-B : ℕ
  id-B = proj₁ fresh-id-B
  new-var-B : id-B ∉ V⟨ B · (` n) ⟩
  new-var-B = proj₂ fresh-id-B
  idb∉B : id-B ∉ V⟨ B ⟩
  idb∉B = x∉v⟨m·n⟩→x∉v⟨m⟩ id-B B (` n) new-var-B
  idb≢n : n ≢ id-B
  idb≢n = non-equality ℕ _≡ᵢ_ (new-identifier 0) 0 V⟨ B · ` n ⟩ n id-B (inj₂ (inj₂ refl))
    λ{ (inj₁ (inj₁ x)) → idb∉B (inj₁ x)
     ; (inj₂ (inj₁ x)) → idb∉B (inj₂ x)
     ; (inj₂ (inj₂ y)) → x∉v⟨m·n⟩→x∉v⟨n⟩ id-B B (` n) new-var-B (inj₂ y) }
  B' : Λ
  B' = subst ℕ _≡ᵢ_ (new-identifier 0) 0 (proj₁ fresh-id-B) n B
  B＝B' : B ＝ B'
  B＝B' = subst-lemma ℕ _≡ᵢ_ (new-identifier 0) 0 id-B n B idb∉B
  n∉VB' : n ∉ V⟨ B' ⟩
  n∉VB' = subst-idem ℕ _≡ᵢ_ (new-identifier 0) 0 id-B n (λ{ x → idb≢n (sym x) }) B
  lemma-one : (I · K · A · B) ＝ A
  lemma-one =
    begin
      I · K · A · B
    ＝⟨ application (application I-simplifies) ⟩
      K · A · B
    ＝⟨ application (extensional A＝A') ⟩ 
      K · A' · B
    ＝⟨ reflexive ⟩
      (ƛ m ⇒ (ƛ n ⇒ ` m)) · A' · B
    ＝⟨ application (β-conversion m (ƛ n ⇒ ` m) A') ⟩
      (ƛ n ⇒ A') · B
    ＝⟨ β-conversion n A' B ⟩
      A' [ n := B ]
    ＝⟨ free-variable-substitution A' B n (x∉v→x∉fv n A' n∉VA') ⟩
      A'
    ＝⟨ symmetric A＝A' ⟩ 
      A
    ∎
  lemma-two : (S · K · A · B) ＝ (K · B · (A · B))
  lemma-two =
    begin
      S · K · A · B
    ＝⟨ application (extensional A＝A') ⟩
      S · K · A' · B
    ＝⟨ reflexive ⟩ 
      (ƛ m ⇒ (ƛ o ⇒ (ƛ n ⇒ (` m · ` n · (` o · ` n))))) · K · A' · B
    ＝⟨ application (application (β-conversion m
                                   (ƛ o ⇒
                                    (ƛ n ⇒
                                     ` m · ` n · (` o · ` n)))
                                     K)) ⟩
      (ƛ o ⇒ (ƛ n ⇒ K · ` n · (` o · ` n))) · A' · B
    ＝⟨ application (β-conversion o (ƛ n ⇒ K · ` n · (` o · ` n)) A') ⟩
      (ƛ n ⇒
         K · ` n · (A' · ` n))
       · B
    ＝⟨ β-conversion n (K · ` n · (A' · ` n)) B ⟩
      K · B · ((A' [ n := B ]) · B)
    ＝⟨ extensional (application (free-variable-substitution A' B n (x∉v→x∉fv n A' n∉VA'))) ⟩
      K · B · (A' · B)
    ＝⟨ extensional (application (symmetric A＝A')) ⟩ 
      K · B · (A · B)
    ∎


I♯S : I ♯ S
I♯S = record { inconsistent = λ x A B → s=i->A=B x }

xx♯xy : {x y : ℕ} → ((` x) · (` x)) ♯ ((` x) · (` y))
xx♯xy = record { inconsistent = λ prop A B → helper prop }
  where
    helper : ∀ {x} {y} (prop : (` x · ` x) ＝ (` x · ` y)) {A} {B} →
         A ＝ B
    helper x =  {!!}
