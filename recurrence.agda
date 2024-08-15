open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level as L using (Level; _⊔_; suc) 
open import Data.Nat.Base using (ℕ; _≤_)
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool using (true; false)
open import Data.Product using (_×_; Σ; _,_)

private
  variable
    a b' c p : Level
    A' : Set a
    B : Set b'
    C : Set c
    
data vec {l : Level} (A' : Set l) : ℕ → Set l where
  [] : vec A' zero
  _∷_ : {n : ℕ} → A' → vec A' n → vec A' (ℕ.suc n)

map : {l : Level} {A' B : Set l} {n : ℕ} → (f : A' → B) → vec A' n → vec B n
map f [] = []
map f (x ∷ x₁) = f x ∷ map f x₁

infixl 4 _⊛_

_⊛_ : ∀ {n} → vec (A' → B) n → vec A' n → vec B n
[]       ⊛ []       = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

dot-product : {n : ℕ} → vec ℕ n → vec ℕ n → ℕ
dot-product [] [] = 0
dot-product (x ∷ xs) (y ∷ ys) = x * y + dot-product xs ys

replicate : ∀ {n} → A' → vec A' n
replicate {n = zero}  x = []
replicate {n = suc n} x = x ∷ replicate x

matrix : {l : Level} (A' : Set l) → ℕ → ℕ → Set l
matrix A' m n = vec (vec A' n) m

transpose : ∀ {m n} → matrix A' n m → matrix A' m n
transpose []         = replicate []
transpose (as ∷ ass) = replicate _∷_ ⊛ as ⊛ transpose ass

mat = matrix

_mat-vec-prod_ : ∀ {m n} → mat ℕ n m → vec ℕ m → vec ℕ n
x mat-vec-prod y = map (dot-product y) x

zero-vec : ∀{n} → vec ℕ n
zero-vec = replicate 0

data list {n : Level} (A : Set n) : Set n where
  [] : list A
  _::_ : (x : A) (xs : list A) → list A

len : {n : Level} → {A : Set n} → list A → ℕ
len [] = 0
len (x :: xs) = Nat.suc (len xs)

data _≤ᵥ_ : {n : ℕ} → vec ℕ n → vec ℕ n → Set where
  empty-lists : (x y : vec ℕ 0) → x ≤ᵥ y
  le-head : {n : ℕ} → (x y : ℕ) → (xs ys : vec ℕ n) → x ≤ y → xs ≤ᵥ ys → (x ∷ xs) ≤ᵥ (y ∷ ys)

record Domain (dim : ℕ) : Set where
 field
   A : mat ℕ dim dim
   b : vec ℕ dim

data null {l : Level} {A : Set l} : Set l where

_^_ : {l : Level} → (A : Set l) → ℕ → Set l
_^_ {l} A zero = null {l} {A}
A ^ Nat.suc n = A × (A ^ n)

record IndexMapping {n : Level} (in-dimension out-dimension : ℕ) (params : list ℕ) : Set where
  field
    IA : mat ℕ in-dimension out-dimension
    IB : mat ℕ (len params) out-dimension
    IC : vec ℕ out-dimension

record Variable {n : Level} (domain-dimension : ℕ) (parameters : list ℕ) : Set n where
  field
    function-arity : ℕ
    domain : Domain domain-dimension
    index-dimension : ℕ
    function : ℕ ^ function-arity → ℕ
    index-mappings : vec (IndexMapping {n} domain-dimension function-arity parameters) function-arity

data None : Set where

Vars : list ℕ → list ℕ → Set 
Vars [] _ = None
Vars (x :: xs) params = Variable x params × Vars xs params
    
record RecurrentSystem {n : Level} : Set (L.suc n) where
  field
    dimension : ℕ
    parameters : list ℕ
    domain-dims : list ℕ
    variables : Vars domain-dims parameters
    

N₁ N₂ N₃ : ℕ
N₁ = 10
N₂ = 11
N₃ = 12

X : ℕ → ℕ → ℕ → ℕ
X₁̣₁ : ℕ → ℕ → ℕ → ℕ
X₂̣₁ : ℕ → ℕ → ℕ → ℕ
Y₁̣₁ : ℕ → ℕ → ℕ → ℕ
Y₁̣₂ : ℕ → ℕ → ℕ → ℕ

{-# TERMINATING #-}
X₁̣₁ 1 1 1 = X N₁ N₂ N₃
X₁̣₁ 1 1 x = X₂̣₁ 1 1 x
X₁̣₁ 1 p₁ p₂ = Y₁̣₁ 1 (p₁ - 1) p₂
X₁̣₁ p₁ p₂ p₃ = Y₁̣₁ (p₁ - 1) p₂ p₃

{-# TERMINATING #-}
Y₁̣₁ 1 1 1 = 0
Y₁̣₁ p₁ p₂ 1 = Y₁̣₂ p₁ p₂ 1
Y₁̣₁ p₁ p₂ p₃ = X₁̣₁ p₁ p₂ (p₃ - 1)

X₂̣₁ _ _ _ = 0

Y₁̣₂ _ _ _ = 0

{-# TERMINATING #-}
X p₁ p₂ p₃ with p₁ == N₁ | p₂ == N₂ | p₃ == N₃
... | true | true | true = X₁̣₁ p₁ p₂ p₃
... |  _   |  _   |  _   = 0
--X₁̣₁ N₁ N₂ N₃
--X _ _ _ = 0


