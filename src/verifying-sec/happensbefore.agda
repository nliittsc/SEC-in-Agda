open import Data.List
  using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
--open import Data.List.Membership.Setoid using (_∈_)
--open import Data.List.Relation.Binary.Permutation.Propositional
--  using (_↭_; ↭-refl; ↭-sym; ↭-trans)
--open import Data.List.Relation.Binary.Permutation.Propositional.Properties
--  using ()
--open import Data.List.Relation.Unary.Unique.Setoid
--  using (Unique)
open import Relation.Binary.Bundles
  using (StrictPartialOrder; Preorder)
open import Relation.Nullary using (¬_)
open import Level using (Level; 0ℓ)

module HappensBefore (hb : StrictPartialOrder 0ℓ 0ℓ 0ℓ) where

  open StrictPartialOrder hb renaming (Carrier to Oper; _<_ to _≺_)



  -- We define concurrency
  data _∥_ : Oper → Oper → Set where

    x∥y : ∀{x y} → ¬ (x ≺ y) → ¬ (y ≺ x) → x ∥ y

  -- Now we can define "consistent with happens before"
  data hb-consistent : List Oper → Set where

    []-con-hb :
      ---------
      hb-consistent []

    ++-con-hb : ∀{y xs}
      → hb-consistent xs
      → (∀(x : Oper) → x ∈ xs → ¬ (y ≺ x))
        --------------------------------------
      → hb-consistent (xs ++ [ y ])


