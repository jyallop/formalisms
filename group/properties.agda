open import group using (Group; Group'; IsGroup)
open import Relation.Binary.Reasoning.Setoid 
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_ ; Σ-syntax; ∃; ∃-syntax; _×_)

module group.properties {g₁ g₂} (G : Group g₁ g₂) where
open Group


ε⁻¹≈ε : ϵ ⁻¹ ≈ ϵ
ε⁻¹≈ε = begin
  (ϵ ⁻¹)      ≈⟨ sym (proj₁ (identity (ϵ ⁻¹))) ⟩
  ((ϵ ⁻¹) · ϵ)  ≈⟨ (proj₁ (inverse ϵ)) ⟩
  ϵ ∎

unique-inverse : ∀ {a b} → (a · b ≈ a) → b ≈ ϵ
unique-inverse {a} {b} prop =
  begin
    b
  ≈⟨ sym (proj₂ (identity b)) ⟩
    ϵ · b
  ≈⟨ ·-congʳ (sym (proj₁ (inverse a))) ⟩
    ((a ⁻¹) · a) · b
  ≈⟨ associative (a ⁻¹) a b ⟩
    (a ⁻¹) · (a · b)
  ≈⟨ ·-congˡ prop ⟩
    (a ⁻¹) · a
  ≈⟨ proj₁ (inverse a) ⟩
    ϵ
  ∎

cancellation-law : { a b c : Obj } → (a · b ≈ a · c) ⊎ (b · a ≈ c · a) → b ≈ c
cancellation-law {a} {b} {c} (inj₁ prop) =
  begin
    b
  ≈⟨ sym (proj₂ (identity b)) ⟩
    ϵ · b
  ≈⟨ ·-congʳ (sym (proj₁ (inverse a))) ⟩
    ((a ⁻¹) · a) · b
  ≈⟨ associative (a ⁻¹) a b ⟩
    (a ⁻¹) · (a · b)
  ≈⟨ ·-congˡ prop ⟩
    (a ⁻¹) · (a · c)
  ≈⟨ sym (associative (a ⁻¹) a c) ⟩
    ((a ⁻¹) · a) · c
  ≈⟨ ·-congʳ (proj₁ (inverse a)) ⟩
    ϵ · c
  ≈⟨ proj₂ (identity c) ⟩
    c
  ∎
cancellation-law {a} {b} {c} (inj₂ prop) =
  begin
    b
  ≈⟨ sym (proj₁ (identity b)) ⟩
    b · ϵ
  ≈⟨ ·-congˡ (sym (proj₂ (inverse a))) ⟩
    b · (a · (a ⁻¹))
  ≈⟨ sym (associative b a (a ⁻¹)) ⟩
    (b · a) · (a ⁻¹)
  ≈⟨ ·-congʳ prop ⟩
    c · a · (a ⁻¹)
  ≈⟨ associative c a (a ⁻¹) ⟩
    c · (a · (a ⁻¹))
  ≈⟨ ·-congˡ (proj₂ (inverse a)) ⟩
    c · ϵ
  ≈⟨ proj₁ (identity c) ⟩
    c
  ∎

unique-inverse-law : {a b : Obj} → a · b ≈ ϵ → (a ≈ b ⁻¹) × (b ≈ a ⁻¹)
unique-inverse-law {a} {b} prop = helperL prop , helperR prop
  where
    helperL : a · b ≈ ϵ → a ≈ b ⁻¹
    helperL prop =
      begin
        a
      ≈⟨ sym (proj₁ (identity a)) ⟩
        a · ϵ
      ≈⟨ ·-congˡ (sym (proj₂ (inverse b))) ⟩
        a · (b · b ⁻¹)
      ≈⟨ sym (associative a b (b ⁻¹)) ⟩
        (a · b) · (b ⁻¹)
      ≈⟨ ·-congʳ prop ⟩
        ϵ · (b ⁻¹)
      ≈⟨ proj₂ (identity (b ⁻¹)) ⟩
        b ⁻¹
      ∎
    helperR : a · b ≈ ϵ → b ≈ a ⁻¹
    helperR prop =
      begin
        b
      ≈⟨ sym (proj₂ (identity b)) ⟩
        ϵ · b
      ≈⟨ ·-congʳ (sym (proj₁ (inverse a))) ⟩
        (a ⁻¹ · a) · b
      ≈⟨ associative (a ⁻¹) a b ⟩
        (a ⁻¹) · (a · b)
      ≈⟨ ·-congˡ prop ⟩
        (a ⁻¹) · ϵ
      ≈⟨ proj₁ (identity (a ⁻¹)) ⟩
        a ⁻¹
      ∎

remove-parens : {a b c d : Obj} → a · b · (c · d) ≈ a · b · c · d
remove-parens {a} {b} {c} {d} =
  begin
    a · b · (c · d)
  ≈⟨ associative a b (c · d) ⟩
    a · (b · (c · d))
  ≈⟨ ·-congˡ (sym (associative b c d)) ⟩
    a · (b · c · d)
  ≈⟨ sym (associative a (b · c) d) ⟩
    a · (b · c) · d
  ≈⟨ ·-congʳ (sym (associative a b c)) ⟩
    a · b · c · d
  ∎

inverse-law : {a b : Obj} → (a · b) ⁻¹ ≈ b ⁻¹ · a ⁻¹
inverse-law {a} {b} = sym (proj₂ (unique-inverse-law helper))
  where
    helper : a · b · (b ⁻¹ · a ⁻¹) ≈ ϵ
    helper =
      begin
        a · b · (b ⁻¹ · a ⁻¹)
      ≈⟨ remove-parens {a} {b} {b ⁻¹} {a ⁻¹} ⟩
        a · b · b ⁻¹ · a ⁻¹
      ≈⟨ ·-congʳ (associative a b (b ⁻¹)) ⟩
        a · (b · (b ⁻¹)) · (a ⁻¹)
      ≈⟨ ·-congʳ (·-congˡ (proj₂ (inverse b))) ⟩
        a · ϵ · a ⁻¹
      ≈⟨ ·-congʳ (proj₁ (identity a)) ⟩
        a · a ⁻¹
      ≈⟨ proj₂ (inverse a) ⟩
        ϵ
      ∎

double-inverse-law : {a : Obj} → (a ⁻¹) ⁻¹ ≈ a
double-inverse-law {a} = sym (proj₁ (unique-inverse-law (proj₂ (inverse a))))

exercise-one : {x : Obj} → x · x ≈ x → x ≈ ϵ
exercise-one {x} prop = trans (sym (proj₂ (identity x)))
                              (trans (·-congʳ (sym (proj₁ (inverse x))))
                              (trans (associative (x ⁻¹) x x)
                              (trans (·-congˡ (helper prop))
                              (trans (sym (associative (x ⁻¹) x ϵ))
                              (trans (·-congʳ (proj₁ (inverse x)))
                              (trans (proj₂ (identity ϵ)) refl))))))
             where
               helper : {x : Obj} → x · x ≈ x → x · x ≈ x · ϵ
               helper {x} prop = trans prop (sym (proj₁ (identity x)))

inverses-commute : {a b : Obj} → a · b ≈ b · a → a ⁻¹ · b ⁻¹ ≈ b ⁻¹ · a ⁻¹
inverses-commute {a} {b} prop =
  begin
    a ⁻¹ · b ⁻¹
  ≈⟨ sym inverse-law ⟩
    (b · a) ⁻¹
  ≈⟨ ⁻¹-cong (sym prop) ⟩
    (a · b) ⁻¹
  ≈⟨ inverse-law ⟩
    b ⁻¹ · a ⁻¹
  ∎

inverse-lemma : {a b : Obj} → a · b ≈ b · a → a ≈ b · a · b ⁻¹
inverse-lemma {a} {b} prop =
  begin
    a
  ≈⟨ sym (proj₁ (identity a)) ⟩
    a · ϵ
  ≈⟨ ·-congˡ (sym (proj₂ (inverse b))) ⟩
    a · (b · (b ⁻¹))
  ≈⟨ sym (associative a b (b ⁻¹)) ⟩
    a · b · (b ⁻¹)
  ≈⟨ ·-congʳ prop ⟩
    b · a · (b ⁻¹)
  ∎

inverse-lemma-two : {a b : Obj} → a · b ≈ b · a → a · b ⁻¹ ≈ b ⁻¹ · a
inverse-lemma-two {a} {b} prop =
  begin
    a · b ⁻¹
  ≈⟨ sym (proj₂ (identity (a · b ⁻¹))) ⟩ 
    ϵ · (a · b ⁻¹)
  ≈⟨ ·-congʳ (sym (proj₁ (inverse b))) ⟩
    (b ⁻¹) · b · (a · (b ⁻¹))
  ≈⟨ associative (b ⁻¹) b (a · (b ⁻¹)) ⟩
    (b ⁻¹) · (b · (a · (b ⁻¹)))
  ≈⟨ ·-congˡ (sym (associative b a (b ⁻¹))) ⟩
    (b ⁻¹) · (b · a · (b ⁻¹))
  ≈⟨ ·-cong (⁻¹-cong refl) (sym (inverse-lemma prop)) ⟩ 
    (b ⁻¹) · a
  ∎
    
inverse-lemma-three : {a b : Obj} → a · b ≈ b · a → a · a · b ≈ a · b · a
inverse-lemma-three {a} {b} prop =
  begin
    a · a · b
  ≈⟨ associative a a b ⟩
    a · (a · b)
  ≈⟨ ·-congˡ prop ⟩
    a · (b · a)
  ≈⟨ sym (associative a b a) ⟩
    a · b · a
  ∎

inverse-lemma-four : {a b : Obj} → a · b ≈ ϵ → b · a ≈ ϵ
inverse-lemma-four {a} {b} prop =
  begin
    b · a
  ≈⟨ ·-congˡ (proj₁ (unique-inverse-law prop)) ⟩
    b · (b ⁻¹)
  ≈⟨ proj₂ (inverse b) ⟩
    ϵ
  ∎

inverse-lemma-five : {a b : Obj} → a · a ≈ ϵ → a ≈ a ⁻¹
inverse-lemma-five {a} {b} prop =
  begin
    a
  ≈⟨ proj₁ (unique-inverse-law prop) ⟩
    a ⁻¹
  ∎

inverse-lemma-six : {a b : Obj} → a ≈ a ⁻¹ → a · a ≈ ϵ
inverse-lemma-six {a} {b} prop =
  begin
    a · a
  ≈⟨ ·-congˡ prop ⟩
    a · (a ⁻¹)
  ≈⟨ proj₂ (inverse a) ⟩
    ϵ
  ∎

inverse-lemma-seven : {a b c : Obj} → c ≈ c ⁻¹ → a · b ≈ c → a · b · c ≈ ϵ
inverse-lemma-seven {a} {b} {c} c≈c prop =
  begin
    a · b · c
  ≈⟨ ·-congʳ prop ⟩
    c · c
  ≈⟨ ·-congˡ c≈c ⟩
   c · (c ⁻¹)
  ≈⟨ proj₂ (inverse c) ⟩
    ϵ
  ∎
    
inverse-lemma-eight : {a b c : Obj} → c ≈ c ⁻¹ → a · b · c ≈ ϵ → a · b ≈ c
inverse-lemma-eight {a} {b} {c} c≈c prop =
  begin
    a · b
  ≈⟨ sym (proj₁ (identity (a · b))) ⟩
    a · b · ϵ
  ≈⟨ ·-congˡ (sym (proj₂ (inverse c))) ⟩
    a · b · (c · (c ⁻¹))
  ≈⟨ remove-parens ⟩
    a · b · c · (c ⁻¹)
  ≈⟨ ·-congʳ prop ⟩
    ϵ · (c ⁻¹)
  ≈⟨ proj₂ (identity (c ⁻¹)) ⟩
    (c ⁻¹)
  ≈⟨ sym c≈c ⟩
    c
  ∎



_^_ : ∀ a → (n : ℕ) → Obj
_ ^ ℕ.zero = ϵ
a ^ (ℕ.suc x) = a · (a ^ x)

power-prop : ∀ {a} → (n : ℕ) → a · a ^ n ≈ a ^ (ℕ.suc n)
power-prop {a} zero = refl
power-prop {a} (ℕ.suc n) = ·-congˡ (power-prop n)

power-law : ∀ {a b} → (n : ℕ) → (b · a · (b ⁻¹)) ^ n ≈ b · (a ^ n) · (b ⁻¹)
power-law {a} {b} zero = begin
         ϵ
       ≈⟨ sym (proj₂ (inverse b)) ⟩
         b · b ⁻¹ 
       ≈⟨ ·-congʳ (sym (proj₁ (identity b))) ⟩
         (b · ϵ) · (b ⁻¹)
       ∎
power-law {a} {b} (ℕ.suc n) = begin
         ((b · a · b ⁻¹) ^ ℕ.suc n)
       ≈⟨ refl ⟩
         (b · a · b ⁻¹) · (b · a · b ⁻¹) ^ n
       ≈⟨ ·-congˡ (power-law n) ⟩
         ((b · a) · b ⁻¹) · ((b · a ^ n) · (b ⁻¹))
       ≈⟨ sym (associative ((b · a) · (b ⁻¹)) (b · (a ^ n)) (b ⁻¹)) ⟩
         ((b · a) · b ⁻¹) · (b · a ^ n) · (b ⁻¹)
       ≈⟨ ·-congʳ (sym (associative ((b · a) · (b ⁻¹)) b (a ^ n))) ⟩
         ((((b · a) · b ⁻¹) · b) · a ^ n) · (b ⁻¹)
       ≈⟨ ·-congʳ (·-congʳ (associative (b · a) (b ⁻¹) b)) ⟩
         (((b · a) · ((b ⁻¹) · b)) · a ^ n) · (b ⁻¹)
       ≈⟨ ·-congʳ (·-congʳ (·-congˡ (proj₁ (inverse b)))) ⟩
         (((b · a) · ϵ) · a ^ n) · (b ⁻¹)
       ≈⟨ ·-congʳ (·-congʳ (proj₁ (identity (b · a)))) ⟩
         ((b · a) · a ^ n) · (b ⁻¹)
       ≈⟨ ·-congʳ (associative b a (a ^ n)) ⟩
         b · (a · a ^ n) · (b ⁻¹)
       ≈⟨ ·-congʳ (·-congˡ (power-prop n)) ⟩
         b · (a ^ ℕ.suc n) · (b ⁻¹)
       ∎

{-# TERMINATING #-}
power-law-two : ∀ {a b} → (n : ℕ) → (a · b) ^ n ≈ (a ^ n) · (b ^ n)
power-law-two {a} {b} zero = sym (proj₁ (identity ϵ))
power-law-two {a} {b} (ℕ.suc n) = 
  begin
    a · b · (a · b) ^ n
   ≈⟨ refl ⟩
     (a · b) ^ (ℕ.suc n)
   ≈⟨ power-law-two (ℕ.suc n) ⟩
    a · (a ^ n) · (b · (b ^ n))
  ∎

power-law-three : ∀ {a} → a ^ 2 ≈ ϵ → ∃[ x ] x ^ 3 ≈ a
power-law-three {a} prop = a ,
  (begin
    a · (a · (a · ϵ))
  ≈⟨ ·-congˡ prop ⟩
    a · ϵ
  ≈⟨ proj₁ (identity a) ⟩ 
    a
  ∎)

power-law-four : ∀ {a} → a ^ 3 ≈ ϵ → ∃[ x ] x ^ 2 ≈ a
power-law-four {a} prop = a ^ 2 ,
  (begin
    a · (a · ϵ) · (a · (a · ϵ) · ϵ)
  ≈⟨ ·-congʳ (·-congˡ (proj₁ (identity a))) ⟩
    ((a · a) · ((a · (a · ϵ)) · ϵ))
  ≈⟨ ·-congˡ (proj₁ (identity (a · (a · ϵ)))) ⟩
    ((a · a) · (a · (a · ϵ)))
  ≈⟨ associative a a (a · (a · ϵ)) ⟩
    (a · (a · (a · (a · ϵ))))
  ≈⟨ ·-congˡ prop ⟩ 
    a · ϵ
  ≈⟨ proj₁ (identity a) ⟩ 
    a
  ∎)
    
power-law-five : ∀ {a} → ∃[ x ] x ^ 3 ≈ a ⁻¹ → ∃[ y ] y ^ 3 ≈ a
power-law-five {a} (x , prop) = (x ⁻¹) ,
  (begin
    x ⁻¹ · (x ⁻¹ · (x ⁻¹ · ϵ))
  ≈⟨ ·-congˡ (·-congˡ (proj₁ (identity (x ⁻¹)))) ⟩
    x ⁻¹ · (x ⁻¹ · x ⁻¹)
  ≈⟨ ·-congˡ (sym inverse-law) ⟩
    x ⁻¹ · (x · x) ⁻¹
  ≈⟨ sym inverse-law ⟩
    (x · x · x) ⁻¹
  ≈⟨ ⁻¹-cong (associative x x x) ⟩
    (x · (x · x)) ⁻¹
  ≈⟨ ⁻¹-cong (·-congˡ (·-congˡ (sym (proj₁ (identity x))))) ⟩
    (x · (x · (x · ϵ))) ⁻¹
  ≈⟨ ⁻¹-cong prop ⟩
    (a ⁻¹) ⁻¹
  ≈⟨ double-inverse-law ⟩
    a
  ∎)


power-law-six : ∀ {a b} → ∃[ x ] x · a · x ≈ b → ∃[ y ] y ^ 2 ≈ a · b
power-law-six {a} {b} (x , prop) = (a · x) ,
  (begin
    (a · x) · ((a · x) · ϵ)
  ≈⟨ ·-congˡ (proj₁ (identity (a · x))) ⟩
    (a · x) · (a · x)
  ≈⟨ associative a x (a · x) ⟩
    a · (x · (a · x))
  ≈⟨ ·-congˡ (sym (associative x a x)) ⟩
    a · (x · a · x)
  ≈⟨ ·-congˡ prop ⟩
    a · b
  ∎)
