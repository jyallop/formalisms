open import Relation.Binary using (Setoid; IsEquivalence; Rel; _Preserves₂_⟶_⟶_; _Preserves_⟶_ )
open import Relation.Unary using (｛_｝; _∉_; Pred; _∪_; _∈_; ∅; Empty; _⊆_)

record Topology : Set₁ where
  field
    base : Set
    subsets : x ⊆ base
