{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module universes where

open import Agda.Primitive public
  renaming (Level to Universe
          ; lzero to 𝓤₀
          ; lsuc to _⁺
          ; Setω to 𝓤ω)
  using (_⊔_)

Type = λ ℓ → Set ℓ

_̇   : (𝓤 : Universe) → Type (𝓤 ⁺)

𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤

infix  1 _̇
