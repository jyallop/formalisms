open import Relation.Unary using (Decidable;｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import identifiers
open import Data.Nat using (ℕ; _≡ᵇ_; zero; suc)
open import alpha-congruence
open import Agda.Builtin.Bool


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
  ＝⟨ application (application K＝K') ⟩ 
    K' · B · (A · B)
  ＝⟨ reflexive ⟩
    (ƛ m ⇒ (ƛ id ⇒ ` m)) · B · (A · B)
  ＝⟨ application (β-conversion m (ƛ id ⇒ ` m) B) ⟩
    ((ƛ id ⇒ ` m) [ m := B ]) · (A · B)
  ＝⟨ application {!reflexive!} ⟩ --application (β-conversion m (ƛ id ⇒ ` m) B) ⟩ 
    (ƛ id ⇒ B) · (A · B) 
  ＝⟨ β-conversion id B (A · B) ⟩ 
    B [ id := (A · B) ]
  ＝⟨ free-variable-substitution B (A · B) id (x∉v→x∉fv id B id∉VB) ⟩
    B
  ∎
  where
  fresh-id : Σ[ x ∈ ℕ ] x ∉ V⟨ A · B · K · S ⟩
  fresh-id = new-identifier 0 (V⟨ A · B · K · S ⟩) λ x → (A · B · K · S) V> x
  id : ℕ
  id = proj₁ fresh-id
  new-var : id ∉ V⟨ A · B · K · S ⟩
  new-var = proj₂ fresh-id
  id∉VA : id ∉ V⟨ A ⟩
  id∉VA = x∉v⟨m·n⟩→x∉v⟨m⟩ id A B (x∉v⟨m·n⟩→x∉v⟨m⟩ id (A · B) K (x∉v⟨m·n⟩→x∉v⟨m⟩ id (A · B · K) S new-var))
  id∉VB : id ∉ V⟨ B ⟩
  id∉VB = x∉v⟨m·n⟩→x∉v⟨n⟩ id A B (x∉v⟨m·n⟩→x∉v⟨m⟩ id (A · B) K (x∉v⟨m·n⟩→x∉v⟨m⟩ id (A · B · K) S new-var))
  id∉VK : id ∉ V⟨ K ⟩
  id∉VK = x∉v⟨m·n⟩→x∉v⟨n⟩ id (A · B) K (x∉v⟨m·n⟩→x∉v⟨m⟩ id (A · B · K) S new-var)
  id∉VS : id ∉ V⟨ S ⟩
  id∉VS = x∉v⟨m·n⟩→x∉v⟨n⟩ id (A · B · K) S new-var
  K' : Λ
  K' = subst ℕ _≡ᵢ_ (new-identifier 0) 0 (proj₁ fresh-id) n K
  K＝K' : K ＝ K'
  K＝K' = subst-lemma ℕ _≡ᵢ_ (new-identifier 0) 0 id n K id∉VK 
  lemma-one : (I · K · A · B) ＝ A
  lemma-one =
    begin
      I · K · A · B
    ＝⟨ application (application I-simplifies) ⟩
      K · A · B
    ＝⟨ application (application K＝K') ⟩ 
      K' · A · B
    ＝⟨ reflexive ⟩
      (ƛ m ⇒ (ƛ id ⇒ ` m)) · A · B
    ＝⟨ application (β-conversion m (ƛ id ⇒ ` m) A) ⟩
      (ƛ id ⇒ ` m) [ m := A ] · B
    ＝⟨ {!!} ⟩ --β-conversion id A B ⟩
      A [ id := B ]
    ＝⟨ free-variable-substitution A B id (x∉v→x∉fv id A id∉VA) ⟩
      A
    ∎
  S' : Λ
  S' = subst ℕ _≡ᵢ_ (new-identifier 0) 0 (proj₁ fresh-id) o S
  S＝S' : S ＝ S'
  S＝S' = subst-lemma ℕ _≡ᵢ_ (new-identifier 0) 0 id o S id∉VS 
  lemma-two : (S · K · A · B) ＝ (K · B · (A · B))
  lemma-two =
    begin
      S · K · A · B
    ＝⟨ application (application (application S＝S')) ⟩ 
      S' · K · A · B
    ＝⟨ reflexive ⟩ 
      (ƛ m ⇒ (ƛ n ⇒ (ƛ id ⇒ (` m · ` id · (` n · ` id))))) · K · A · B
    ＝⟨ {!!} ⟩
      ((ƛ n ⇒ (ƛ id ⇒ (` m · ` id · (` n · ` id)))) [ m := K ]) · A · B
    ＝⟨ application {!!} ⟩  --application (application (β-conversion m
        --                           (ƛ n ⇒
       --                             (ƛ o ⇒
        --                             ` m · ` o · (` n · ` o)))
        --                           K)) ⟩
      (ƛ n ⇒
        (ƛ id ⇒
         K · ` id · (` n · ` id)))
       · A
       · B
    ＝⟨ {!!} ⟩ -- application (β-conversion n (ƛ id ⇒ K · ` id · (` n · ` id)) A) ⟩
      (ƛ id ⇒
         K · ` id · (A · ` id))
       · B
    ＝⟨ β-conversion id (K · ` id · (A · ` id)) B ⟩
      (K · ` id · (A · ` id)) [ id := B ]
    ＝⟨ {!!} ⟩ 
      K · B · ((A [ id := B ]) · B)
    ＝⟨ {!!} ⟩ --extensional (application (free-variable-substitution A B id {!!})) ⟩
      K · B · (A · B)
    ∎


I♯S : I ♯ S
I♯S = record { inconsistent = λ x A B → s=i->A=B x }

xx♯xy : {x y : ℕ} → ((` x) · (` x)) ♯ ((` x) · (` y))
xx♯xy = record { inconsistent = λ prop A B → helper prop }
  where
    helper : ∀ {x} {y} (prop : (` x · ` x) ＝ (` x · ` y)) {A} {B} →
         A ＝ B
    helper x =  {!o!}
