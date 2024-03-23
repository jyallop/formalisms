open import group

-- left-identity : (x : ℤ) → x + 0ℤ ≡ x
-- left-identity (ℤ.pos zero) = Group.refl
-- left-identity (ℤ.pos (Data.Nat.Base.suc n)) rewrite +-identityʳ n = Group.refl
-- left-identity (ℤ.negsuc n) with 0 ⊖ Data.Nat.Base.suc n
-- ... | n = refl


-- right-identity : (x : ℤ) → 0ℤ + x ≡ x
-- right-identity x rewrite +-comm 0ℤ x rewrite left-identity x = refl

-- left-inverse : (x : ℤ) → - x + x ≡ 0ℤ
-- left-inverse (ℤ.pos zero) = refl
-- left-inverse (ℤ.pos (Data.Nat.Base.suc n)) = Data.Integer.Properties.n⊖n≡0 (Data.Nat.Base.suc n)
-- left-inverse (ℤ.negsuc n) = Data.Integer.Properties.n⊖n≡0 (Data.Nat.Base.suc n)

-- right-inverse : (x : ℤ) → x + (- x) ≡ 0ℤ
-- right-inverse x rewrite +-comm x (- x) = left-inverse x

-- additive : Group _ _ 
-- additive = record {
--   Obj = ℤ;
--   _·_ = _+_;
--   _≈_ = _≡_; 
--   equivalence = record { refl = refl ; sym = λ { refl → refl }; trans = λ { refl refl → refl } };
--   ϵ = 0ℤ;
--   _⁻¹ = -_;
--   identity = (λ x → (left-identity x) , (right-identity x));
--   inverse = λ x → left-inverse x , right-inverse x;
--   associative = Data.Integer.Properties.+-assoc
--   }



