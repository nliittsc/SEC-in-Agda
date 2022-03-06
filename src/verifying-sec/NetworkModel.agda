module NetworkModel where


open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using ()
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans)

open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Utils.List using (Distinct)



-- Denotes an arbritrary event
data Event {Msg : Set} : Set where

  broadcast : Msg → Event
  deliver : Msg → Event


-- Asserts the proposition that a function `history` is a node history
record IsNodeHistory {A : Set} (history : ℕ → List A) : Set where

  field
    histories-distinct : ∀ i → Distinct (history i)

-- Denotes the type of Node Histories
record NodeHistory : Set₁ where


  field
    Msg : Set
    History : ℕ → List (Event {Msg})
    isNodeHistory : IsNodeHistory History

  open IsNodeHistory isNodeHistory public

  -- A notion of "comes before" in a node history
  data _⊏[_]_ : Event {Msg} → ℕ → Event {Msg} → Set where

    x⊏ᵢy : ∀ x y i
      → ∃[ xs ](∃[ ys ](∃[ zs ]( xs ++ [ x ] ++ ys ++ [ y ] ++ zs ≡ History i )))
      → x ⊏[ i ] y


-- The proposition that we have a network
record IsNetwork {MsgId : Set}
                 (node-history : NodeHistory)
                 (msg-id : (NodeHistory.Msg node-history) → MsgId)
                 : Set where

  open NodeHistory node-history
    renaming (History to history)
    
  field
    
    delvery-has-cause : ∀ {i m}
      → deliver m ∈ history i
      → ∃[ j ] broadcast m ∈ history j
    deliver-locally : ∀ {i m}
      → broadcast m ∈ history i
      → broadcast m ⊏[ i ] deliver m
    msg-id-unique : ∀ {m1 m2 i j}
      → broadcast m1 ∈ history i
      → broadcast m2 ∈ history j
      → msg-id m1 ≡ msg-id m2
      → i ≡ j × m1 ≡ m2


-- An abstract type representing networks
record Network : Set₁ where

  field
    MsgId : Set
    node-history : NodeHistory
    msg-id : NodeHistory.Msg node-history → MsgId
    isNetwork : IsNetwork node-history msg-id

  open IsNetwork isNetwork public

  open NodeHistory node-history public
  
  data _≺_ : Msg → Msg → Set where

    rule1 : ∀ {m1 m2 i}
      → broadcast m1 ⊏[ i ] broadcast m2
      → m1 ≺ m2

    rule2 : ∀{m1 m2 i}
      → deliver m1 ⊏[ i ] broadcast m2
      → m1 ≺ m2

    rule3 : ∀{m1 m2 m3}
      → m1 ≺ m2 → m2 ≺ m3
      → m1 ≺ m3



-- The proposition that network is a 'causal' network
record IsCausalNetwork (network : Network) : Set where

  open Network network public
  
  field
    causal-delivery : ∀ {m1 m2 i}
      → deliver m2 ∈ History i
      → m1 ≺ m2
      → deliver m1 ⊏[ i ] deliver m2

-- The type of all causal networks
record CausalNetwork : Set₁ where

  field
    network : Network
    isCausalNetwork : IsCausalNetwork network



    
    
