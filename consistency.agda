open import lambda-calculus
open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)


record _♯_ (m n : Λ) : Set₁ where
  field
    inconsistent : m ＝ n → ((A B : Λ) → A ＝ B)

-- We define our own versions of the combinators here because I don't feel like dealing with
-- the additional closed term stuff I defined in the combinators module
-- They will be used to test our definition of inconsistency
-- I ♯ K, I ♯ S, and (x y : Λ) → xx ♯ xxy are all proved below
-- These are all exercises from The Lambda Calculus, its Syntax and Semantics by Henk Barendregt
I : Λ
I = ƛ ("x", 0) ⇒ ` ("x", 0)

K : Λ
K = ƛ ("x", 0) ⇒ (ƛ ("y", 0) ⇒ ` ("x", 0))

S : Λ
S = ƛ ("x", 0) ⇒ (ƛ ("y", 0) ⇒ (ƛ ("z", 0) ⇒ (` ("x", 0) · ` ("z", 0) · (` ("y", 0) · ` ("z", 0))))) 

open ＝-Reasoning

I-simplifies : {A : Λ} → (I · A) ＝ A
I-simplifies {A} =
  begin
    I · A
  ＝⟨ β-conversion ("x" , 0) (` ("x" , 0)) A ⟩ 
    A
  ∎

--The ultimate goal is to prove I = K is inconsistent as an axiom
-- we start by proving I = K ­> I = A to A is any lambda term
k=i->i=A : {A : Λ} → I ＝ K → I ＝ A
k=i->i=A {A} prop =
  begin
    I
  ＝⟨ reflexive k-x-y=x ⟩
    K · x · y
  ＝⟨ reflexive (application i-x=k-x) ⟩
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
      ＝⟨ identity ⟩
        (ƛ ("x" , 0) ⇒ ƛ ("y" , 0) ⇒ ` ("x" , 0)) · x · y
      ＝⟨ application (β-conversion ("x" , 0) (ƛ "y" , 0 ⇒ ` ("x" , 0)) x) ⟩
        (ƛ ("y" , 0) ⇒ x) · y
      ＝⟨ β-conversion ("y" , 0) x y ⟩
        x
      ∎
    i-x=k-x : (I · x) ＝ (K · x)
    i-x=k-x = application prop
    i-x-y=x-y : (I · x · y) ＝ (x · y)
    i-x-y=x-y = 
      begin
        I · x · y
      ＝⟨ identity ⟩
        ((ƛ ("x" , 0) ⇒ ` ("x" , 0)) · x) · y
      ＝⟨ application (β-conversion ("x" , 0) (` ("x" , 0)) x) ⟩
         ((` ("x" , 0)) [ ("x" , 0) := x ]) · y
      ＝⟨ identity ⟩
        x · y
      ∎
    x-y=a : (x · y) ＝ A
    x-y=a =
      begin
        x · y
      ＝⟨ identity ⟩
        x · A
      ＝⟨ β-conversion ("x" , 0) (` ("x" , 0)) A ⟩
        A
      ∎

-- We finish the goal proposition through two applications of the above proof
k=i-inconsistent : {A B : Λ} → I ＝ K → A ＝ B
k=i-inconsistent {A} {B} prop =
  begin
    A
  ＝⟨ reflexive (k=i->i=A prop) ⟩
    I
  ＝⟨ k=i->i=A prop ⟩ 
    B
  ∎

-- We can finally say that I = K is in fact inconsistent
I♯K : I ♯ K
I♯K = record {
  inconsistent = λ x A B → k=i-inconsistent x
  }


--This proof relies on more free variable shenanigans, the _s are looking for proof of the following:
-- 1. ("y", 0) ∉ FV⟨ B ⟩
-- 2. ("y", 0) ∉ FV⟨ A ⟩
-- 3. ("z", 0) ∉ FV⟨ A ⟩
s=i->A=B : {A B : Λ} → I ＝ S → A ＝ B
s=i->A=B {A} {B} prop =
  begin
    A
  ＝⟨ reflexive lemma-one ⟩
    I · K · A · B
  ＝⟨ application (application (application prop)) ⟩
    S · K · A · B
  ＝⟨ lemma-two ⟩ 
    K · B · (A · B)
  ＝⟨ application (β-conversion ("x" , 0) (ƛ "y" , 0 ⇒ ` ("x" , 0)) B) ⟩ 
    (ƛ ("y", 0) ⇒ B) · (A · B)
  ＝⟨ β-conversion ("y" , 0) B (A · B) ⟩
    B [ ("y", 0) := (A · B) ]
  ＝⟨ free-variable-substitution B (A · B) ("y" , 0) _ ⟩ 
    B
  ∎
  where
  lemma-one : (I · K · A · B) ＝ A
  lemma-one =
    begin
      I · K · A · B
    ＝⟨ application (application I-simplifies) ⟩
      K · A · B
    ＝⟨ application (β-conversion ("x" , 0) (ƛ "y" , 0 ⇒ ` ("x" , 0)) A) ⟩
      (ƛ ("y", 0) ⇒ A) · B
    ＝⟨ β-conversion ("y" , 0) A B ⟩
      A [ ("y", 0) := B ]
    ＝⟨ free-variable-substitution A B ("y" , 0) _ ⟩ 
      A
    ∎
  lemma-two : (S · K · A · B) ＝ (K · B · (A · B))
  lemma-two =
    begin
      S · K · A · B
    ＝⟨ application (application (β-conversion ("x" , 0)
                                   (ƛ "y" , 0 ⇒
                                    (ƛ "z" , 0 ⇒
                                     ` ("x" , 0) · ` ("z" , 0) · (` ("y" , 0) · ` ("z" , 0))))
                                   K)) ⟩
      (ƛ "y" , 0 ⇒
        (ƛ "z" , 0 ⇒
         K · ` ("z" , 0) · (` ("y" , 0) · ` ("z" , 0))))
       · A
       · B
    ＝⟨ application (β-conversion ("y" , 0) (ƛ "z", 0 ⇒ K · ` ("z", 0) · (` ("y", 0) · ` ("z", 0))) A) ⟩
      (ƛ "z" , 0 ⇒
         K · ` ("z" , 0) · (A · ` ("z" , 0)))
       · B
    ＝⟨ β-conversion ("z" , 0) (K · ` ("z" , 0) · (A · ` ("z" , 0))) B ⟩
      (K · ` ("z" , 0) · (A · ` ("z" , 0))) [ ("z", 0) := B ]
    ＝⟨ identity ⟩ 
      K · B · ((A [ ("z" , 0) := B ]) · B)
    ＝⟨ extensional (application (free-variable-substitution A B ("z" , 0) _)) ⟩
      K · B · (A · B)
    ∎


I♯S : I ♯ S
I♯S = record { inconsistent = λ x A B → s=i->A=B x }

xx♯xy : {x y : Λ} → (x · x) ♯ (x · y)
xx♯xy = {!!}
