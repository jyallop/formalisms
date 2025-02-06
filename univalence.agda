{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import universes public

-- \MCU for 𝓤

variable 𝓤 𝓥 𝓦 𝓣 : Universe

-- \^. for ̇
-- \b1 for 𝟙

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

-- \Pi for Π
𝟙-induction : (A : 𝟙 → 𝓤 ̇ ) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙 : {X : 𝓤 ̇ } → X → 𝟙
!𝟙 _ = ⋆

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
  where
    h : (n : ℕ) → A n
    h zero     = a₀
    h (succ x) = f x (h x)

ℕ-recursion : (X : 𝓤 ̇)
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇)
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where
  _+_  _×_ : ℕ → ℕ → ℕ

  x + y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_

module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
  _≤_ = ℕ-iteration (ℕ → 𝓤₀ ̇) (λ y → 𝟙)
                    λ f → ℕ-recursion (𝓤₀ ̇) 𝟘 λ y P → f y

  x ≥ y = y ≤ x

  _≤'_  : ℕ → ℕ → 𝓤₀ ̇
  0      ≤' y      = 𝟙
  succ x ≤' 0      = 𝟘
  succ x ≤' succ y = x ≤ y

  infix 10 _≤'_
  infix 10 _≤_
  infix 10 _≥_

  definition-forward : (x y : ℕ) → x ≤ y → x ≤' y
  definition-forward zero y prop = prop
  definition-forward (succ x) (succ y) prop = prop

  definition-backward : (x y : ℕ) → x ≤' y → x ≤ y
  definition-backward zero y prop = prop
  definition-backward (succ x) (succ y) prop = prop


data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : (𝓤 ⊔ 𝓥) ̇ where
  inl : X → X + Y
  inr : Y → X + Y

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ = +-induction A
                      (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                      (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

record Σ {𝓤 𝓥} {X : 𝓤 ̇} (Y : X → 𝓥 ̇) : (𝓤 ⊔ 𝓥)̇ where
  constructor
    _,_
  field
    x : X
    y : Y x

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ[ x ] X , y

pr₁ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (x : Σ Y) → Y (pr₁ x)
pr₂ (x , y) = y

Σ-induction : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → A (x , y))
      → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)

_×_ : 𝓤 ̇ → 𝓥 ̇ → (𝓤 ⊔ 𝓥) ̇
X × Y = Σ λ(x : X) → Y

∏ : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
∏ {𝓤} {𝓥} {X} A = (x : X) → A x

-∏ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-∏ X Y = ∏ Y

id : {X : 𝓤 ̇} → X → X
id x = x

id⋆ : (X : 𝓤 ̇) → X → X
id⋆ X = id

_·_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g · f = λ x → g (f x)

domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇} → X → 𝓤 ̇
type-of {𝓤} {X} x = X

data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇ where
  refl : (x : X) → Id X x x

_＝_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ＝ y = Id _ x y

𝕁 : (X : 𝓤 ̇) (A : (x y : X) → x ＝ y → 𝓥 ̇)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ＝ y) → A x y p
𝕁 X A f x x (refl x) = f x

ℍ : (X : 𝓤 ̇) (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇)
  → B x (refl x)
  → (y : X) → (p : x ＝ y) → B y p
ℍ X x B b x (refl x) = b

ℍ' : (X : 𝓤 ̇) (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇)
   → B x (refl x)
   → (y : X) → (p : x ＝ y) → B y p
ℍ' X x B b = {!!}

𝕁' : (X : 𝓤 ̇) (A : (x y : X) → x ＝ y → 𝓥 ̇)
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ＝ y) → A x y p
𝕁' X A f x = ℍ X x (A x) (f x)

ℍs-agreement :  (X : 𝓤 ̇ ) (x : X) (B : (y : X) → x ＝ y → 𝓥 ̇ )
             → (b : B x (refl x)) → (y : X) (p : x ＝ y)
             → ℍ X x B b y p ＝ ℍ' X x B b y p
ℍs-agreement = {!!}

𝕁s-agreement :  (X : 𝓤 ̇ ) (A : (x y : X) → x ＝ y → 𝓥 ̇ )
                (f : (x : X) → A x x (refl x)) (x y : X) (p : x ＝ y)
             → 𝕁 X A f x y p ＝ 𝕁' X A f x y p
𝕁s-agreement X A f x x (refl x) = refl (f x)

module exercises_one where
  open ℕ-order

  0+x=x : {x : ℕ} → (0 Arithmetic.+ x) ＝ x
  0+x=x = {!!}

  sucx≤y→x≤sucy : (x y : ℕ) → (succ x) ≤ y → x ≤ (succ y)
  sucx≤y→x≤sucy = {!!}

  exOne : (x y : ℕ) → x ≤ y → Σ[ z ] ℕ , ((x Arithmetic.+ z) ＝ y)
  exOne = ℕ-induction (λ x → (y : ℕ) → x ≤ y → -Σ ℕ (λ z → (x Arithmetic.+ z) ＝ y)) (λ y prop → y , 0+x=x)
      (λ{ n f →
        ℕ-induction (λ z → succ n ≤ z → -Σ ℕ (λ z₁ → (succ n Arithmetic.+ z₁) ＝ z))
        (λ imp → !𝟘 (-Σ ℕ (λ z₁ → (succ n Arithmetic.+ z₁) ＝ 0)) imp)
        (λ n' f' prop → {!!} )})

  exTwo : {x y : ℕ} → (x ≤ y) ＝ (Σ[ z ] ℕ , ((x Arithmetic.+ z) ＝ y))
  exTwo = {!!}


