module Inc-Dec-Counter where


open import Data.Integer using (ℤ; suc; pred; _+_; _-_; +_; -[1+_]; -_)
open import Data.Integer.Properties using (pred-suc; suc-pred)
--open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Utils.Arrow using (_▷_)
open import Utils.Extension using (extensionality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)



data Operation : Set where

  inc : Operation

  dec : Operation


-- increment-decrement counter state transformer
counter-op : Operation → ℤ → Maybe ℤ
counter-op inc x = just (suc x)
counter-op dec x = just (pred x)

-- incrementing and decrementing 'state' operations commute
counter-ops-commute : ∀ x y z → (counter-op x ▷ counter-op y) z ≡ (counter-op y ▷ counter-op x) z
counter-ops-commute inc inc z = refl
counter-ops-commute dec dec z = refl
counter-ops-commute inc dec z =
  begin
    (counter-op inc ▷ counter-op dec) z
  ≡⟨⟩
    (λ z' → just (pred (suc z'))) z
  ≡⟨⟩
    just (pred (suc z))
  ≡⟨ cong just (pred-suc z) ⟩
    just z
  ≡⟨ cong just (sym (suc-pred z)) ⟩
    just (suc (pred z))
  ≡⟨⟩
    (counter-op dec ▷ counter-op inc) z
  ∎
counter-ops-commute dec inc z = sym (counter-ops-commute inc dec z)


-- Agda version of `locale counter = network-with-ops - counter-op 0`
-- is something like:
-- record counter 
