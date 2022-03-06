module Utils.List where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

data Distinct {A : Set} : List A → Set where

  [] : Distinct []

  _∷_ : ∀ x xs → Distinct xs → ¬ (x ∈ xs) → Distinct (x ∷ xs)
  

