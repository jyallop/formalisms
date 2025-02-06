open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import identifiers
open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)

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
-- I ♯ K, I ♯ S, and (x y : Λ) → xx ♯ xxy are all proved below
-- These are all exercises from The Lambda Calculus, its Syntax and Semantics by Henk Barendregt
I : Λ
I = ƛ m ⇒ (` m)

K : Λ
K = ƛ m ⇒ (ƛ n ⇒ (` m))

S : Λ
S = ƛ m ⇒ (ƛ n ⇒ (ƛ o ⇒ (` m · ` o · (` n · ` o)))) 

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


--This proof relies on more free variable shenanigans, the _ blanks are looking for proof of the following:
-- 1. ("y", 0) ∉ FV⟨ B ⟩
-- 2. ("y", 0) ∉ FV⟨ A ⟩
-- 3. ("z", 0) ∉ FV⟨ A ⟩
s=i->A=B : {A B : Λ} → I ＝ S → A ＝ B
s=i->A=B {A} {B} prop =
  begin
    A
  ＝⟨ symmetric lemma-one ⟩
    I · K · A · B
  ＝⟨ application (application (application prop)) ⟩
    S · K · A · B
  ＝⟨ lemma-two ⟩ 
    K · B · (A · B)
  ＝⟨ application (β-conversion m (ƛ n ⇒ ` m) B) ⟩ 
    (ƛ n ⇒ B) · (A · B)
  ＝⟨ β-conversion n B (A · B) ⟩
    B [ n := (A · B) ]
  ＝⟨ free-variable-substitution B (A · B) n {!!} ⟩ 
    B
  ∎
  where
  id-one :  Σ[ x ∈ ℕ ] x ∉ FV⟨ B ⟩ 
  id-one = new-identifier {!!} (λ z → FV⟨ B ⟩ z) {!!}
  lemma-one : (I · K · A · B) ＝ A
  lemma-one =
    begin
      I · K · A · B
    ＝⟨ application (application I-simplifies) ⟩
      K · A · B
    ＝⟨ application (β-conversion m (ƛ n ⇒ ` m) A) ⟩
      (ƛ n ⇒ A) · B
    ＝⟨ β-conversion n A B ⟩
      A [ n := B ]
    ＝⟨ free-variable-substitution A B n _ ⟩ 
      A
    ∎
  lemma-two : (S · K · A · B) ＝ (K · B · (A · B))
  lemma-two =
    begin
      S · K · A · B
    ＝⟨ application (application (β-conversion m
                                   (ƛ n ⇒
                                    (ƛ o ⇒
                                     ` m · ` o · (` n · ` o)))
                                   K)) ⟩
      (ƛ n ⇒
        (ƛ o ⇒
         K · ` o · (` n · ` o)))
       · A
       · B
    ＝⟨ application (β-conversion n (ƛ o ⇒ K · ` o · (` n · ` o)) A) ⟩
      (ƛ o ⇒
         K · ` o · (A · ` o))
       · B
    ＝⟨ β-conversion o (K · ` o · (A · ` o)) B ⟩
      (K · ` o · (A · ` o)) [ o := B ]
    ＝⟨ reflexive ⟩ 
      K · B · ((A [ o := B ]) · B)
    ＝⟨ extensional (application (free-variable-substitution A B o _)) ⟩
      K · B · (A · B)
    ∎


I♯S : I ♯ S
I♯S = record { inconsistent = λ x A B → s=i->A=B x }

xx♯xy : {x y : Λ} → (x · x) ♯ (x · y)
xx♯xy = record { inconsistent = λ prop A B → helper prop }
  where
  helper : ∀ {A} {B} → {x y : Λ} → (x · x) ＝ (x · y) → A ＝ B
  helper {A} {B} prop =
    begin
      A
    ＝⟨ {!!} ⟩
      B
    ∎
  x : ℕ
  x = 1
  f : Λ
  f = (ƛ x ⇒ S · K · (` x))
