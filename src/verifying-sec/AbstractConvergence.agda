{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module AbstractConvergence where


open import Relation.Nullary using (¬_)
--open import Relation.Binary using (Trichotomous; Total; Tri)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List --using (List; []; _∷_; [_]; _++_; foldl; foldr; map; last; head)
open import Data.List.Properties
  --using (++-assoc; ++-identityʳ-unique; ++-identityˡ-unique; ++-conicalˡ; ++-conicalʳ; ∷ʳ-injectiveˡ)
open import Data.List.Relation.Unary.Linked
  using (Linked; [-])
  renaming (head to linkedHead; tail to linkedTail; head′ to linkedHead';  _∷′_ to _∷ᴸ_)
open import Data.List.Relation.Unary.Linked.Properties
  using (++⁺; AllPairs⇒Linked; Linked⇒AllPairs)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using ()
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.AllPairs.Properties
  renaming (++⁺ to ++-pairs)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-sym; ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (↭-empty-inv; ↭-singleton-inv; ¬x∷xs↭[]; drop-∷)
  renaming (++-identityˡ to ↭-++-identityˡ; ++-identityʳ to ↭-++-identityʳ)
open import Data.List.Relation.Unary.Unique.Setoid
  using (Unique)
open import Relation.Binary.Bundles
  using (StrictPartialOrder; TotalPreorder)
open import Relation.Binary.Structures
  using (IsStrictPartialOrder; IsTotalPreorder; IsEquivalence; IsTotalOrder)
open import Level using (Level; 0ℓ)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Relation.Binary.Connected
  using (Connected; just; nothing; just-nothing; nothing-just)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; cong-app; subst₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


open import Utils.List using (Distinct)
open import Utils.Arrow using (_▷_; _◁_)

private
  variable
    A B C : Set
    Oper State : Set


_≢_ : A → A → Set
x ≢ y = ¬ (x ≡ y)

-- lmao this works?
pattern ∅ = ()


-- Useful rewrite rules
xs++[]≡xs : ∀ {A : Set} → (xs : List A) → xs ++ [] ≡ xs
xs++[]≡xs [] = refl
xs++[]≡xs (x ∷ xs) rewrite xs++[]≡xs xs = refl

{-# REWRITE xs++[]≡xs #-}

-- Silly lemma
x∷xs≢[] : ∀{x : A} {xs : List A} → (x ∷ xs) ≢ []
x∷xs≢[] = λ()

xs∷ʳx≢[] : ∀{x : A} {xs} → (xs ∷ʳ x) ≢ []
xs∷ʳx≢[] {xs = []} = λ ()
xs∷ʳx≢[] {xs = x ∷ xs} = λ ()

-- append is injective
xs≡ys→x∷xs≡x∷ys : ∀(x : A) {xs ys : List A} → xs ≡ ys → x ∷ xs ≡ x ∷ ys
xs≡ys→x∷xs≡x∷ys x xs≡ys = cong (x ∷_) xs≡ys


-- Useful lemmas about lists
++-assoc2 : ∀ xs ys zs (z : Oper) →
        xs ++ ys ≡ (zs ++ [ z ]) ++ ys →
        xs ++ ys ≡ zs ++ ([ z ] ++ ys)
++-assoc2 xs ys zs z f = trans f (++-assoc zs [ z ] ys)

-- We can always construct a snoc operation from a non-empty list
∃snoc : ∀ (xs : List A) → xs ≢ [] → ∃[ y ] (∃[ ys ] xs ≡ ys ++ [ y ])
∃snoc [] xs≢[] = ⊥-elim (xs≢[] refl)
∃snoc (x ∷ []) xs≢[] = x , ([] , refl)
∃snoc (x₁ ∷ x₂ ∷ xs) xs≢[] =
  let
    ind-hyp = ∃snoc (x₂ ∷ xs) x∷xs≢[]
    y = proj₁ ind-hyp
    ys = proj₁ (proj₂ ind-hyp)
    x₂∷xs≡ys++[y] = proj₂ (proj₂ ind-hyp)
  in y , x₁ ∷ ys , cong (x₁ ∷_) x₂∷xs≡ys++[y]
    


-- Every list is either empty or has a last element
xs≡[]∨∃snoc : ∀ {A : Set} → (xs : List A) → (xs ≡ []) ⊎ (∃[ y ] (∃[ ys ] (xs ≡ ys ++ [ y ])))
xs≡[]∨∃snoc [] = inj₁ refl
xs≡[]∨∃snoc (x ∷ xs) = inj₂ (∃snoc (x ∷ xs) x∷xs≢[])
    
-- impossible case
bad↭ : ∀ {x₁ x₂ y} {xs : List A} → ¬ (x₁ ∷ x₂ ∷ xs ↭ y ∷ [])
bad↭ (_↭_.prep _ x∷xs↭[]) = ⊥-elim (¬x∷xs↭[] x∷xs↭[])
bad↭ (_↭_.trans s₁ s₂) with ↭-singleton-inv s₂
... | refl = bad↭ s₁


module happens-before (_≈_ : Oper → Oper → Set)  -- equivalence
                      (_≼_ : Oper → Oper → Set)  -- hb-weak
                      (isTotalPreorder : IsTotalPreorder _≈_ _≼_)
                      (_≺_ : Oper → Oper → Set)  -- hb
                      (isStrictPartialOrder : IsStrictPartialOrder _≈_ _≺_)
                      (interp : Oper → State → Maybe State) where

  open IsTotalPreorder isTotalPreorder renaming (refl to ≈-refl; trans to ≼-trans)
  open IsStrictPartialOrder isStrictPartialOrder renaming (trans to ≺-trans)
  _≻_ : Oper → Oper → Set
  x ≻ y = y ≺ x
  ⟨_⟩ : Oper → State → Maybe State
  ⟨ x ⟩ = interp x

  -- Definition of concurrency
  record _∥_ (x y : Oper) : Set where

    field
      ¬x≺y : ¬ (x ≺ y)
      ¬y≺x : ¬ (y ≺ x)

  open _∥_ public

  private
    variable
      x y : Oper
  -- Some lemmas about concurrency
  ∥⁺ : ¬ x ≺ y → ¬ y ≺ x → x ∥ y
  ∥⁺ ¬x≺y ¬y≺x = record { ¬x≺y = ¬x≺y ; ¬y≺x = ¬y≺x }

  ∥-elimˡ : x ∥ y → ¬ x ≺ y
  ∥-elimˡ record { ¬x≺y = ¬x≺y ; ¬y≺x = ¬y≺x } = ¬x≺y

  ∥-elimʳ : x ∥ y → ¬ y ≺ x
  ∥-elimʳ record { ¬x≺y = ¬x≺y ; ¬y≺x = ¬y≺x } = ¬y≺x

  -- Concurrency is reflexive
  ∥-refl : x ∥ x
  ∥-refl {x} = record
                 { ¬x≺y =
                     IsStrictPartialOrder.irrefl isStrictPartialOrder
                     (IsEquivalence.refl
                      (IsStrictPartialOrder.isEquivalence isStrictPartialOrder))
                 ; ¬y≺x =
                     IsStrictPartialOrder.irrefl isStrictPartialOrder
                     (IsEquivalence.refl
                      (IsStrictPartialOrder.isEquivalence isStrictPartialOrder))
                 }
  -- Concurrency is symmetric. I.e., ops x and y commute
  ∥-sym : x ∥ y → y ∥ x
  ∥-sym record { ¬x≺y = ¬x≺y ; ¬y≺x = ¬y≺x } = record { ¬x≺y = ¬y≺x ; ¬y≺x = ¬x≺y }

  -- The definition of a concurrent (multi-) set
  concurrent-set : ∀(xs : List Oper) → Set
  concurrent-set xs = Linked _∥_ xs

  -- This relation is the closure of happens-before and concurrency
  data _≺*_ (x y : Oper) : Set where

    x-hb-y : x ≺ y → x ≺* y

    x-concurrent-y : x ∥ y → x ≺* y

  data _*≻_ (x y : Oper) : Set where

    y-hb-x : x ≻ y → x *≻ y

    x-concurrent-y : y ∥ x → x *≻ y

  -- The definition of happens-before consistent list
  hb-consistent : ∀(xs : List Oper) → Set
  hb-consistent xs = Linked _*≻_ xs

  hb-singleton : ∀ x → hb-consistent [ x ]
  hb-singleton x = [-]

  hb-cong : ∀ {xs ys} → hb-consistent xs → xs ≡ ys → hb-consistent ys
  hb-cong hb-xs xs≡ys = subst hb-consistent xs≡ys hb-xs

  hb-elimʳ : ∀ xs ys → hb-consistent (xs ++ ys) → hb-consistent ys
  hb-elimʳ [] ys hb-xs++ys = hb-xs++ys
  hb-elimʳ (x ∷ xs) ys hb-xs++ys = hb-elimʳ xs ys (linkedTail hb-xs++ys)

  hb-head-elim : ∀ {x xs} → hb-consistent (x ∷ xs) → hb-consistent xs
  hb-head-elim hb-x∷xs = linkedTail hb-x∷xs



  ¬-elim : ∀ {A : Set} → ¬ A → A → ⊥
  ¬-elim ¬x x = ¬x x

  ⊥-lemma' : ∀ {x : A} {xs} →  x ∷ xs ≡ [] → ⊥
  ⊥-lemma' x∷xs≡[] = ¬-elim x∷xs≢[] x∷xs≡[]

  -- Contradiction for snoc lists
  ⊥-lemma₁ : ∀ {x : A} {xs} → xs ∷ʳ x ≡ [] → ⊥
  ⊥-lemma₁ xs∷ʳx≡[] = ¬-elim xs∷ʳx≢[] xs∷ʳx≡[]

  postulate
    ⊥-lemma₂ : ∀{x y z : A} {xs} → xs ∷ʳ x ∷ʳ y ≡ z ∷ [] → ⊥
    --⊥-lemma₂ {xs = x ∷ xs} xs∷ʳx∷ʳy≡[] = {!!}

  ++-inj-lemma₁ : ∀ {x y : A} {xs} →
                  xs ∷ʳ x ≡ y ∷ [] →
                  x ≡ y
  ++-inj-lemma₁ {xs = xs} xs∷ʳx≡y∷[] = ∷ʳ-injectiveʳ xs [] xs∷ʳx≡y∷[]


  ++-inj-lemma₂ : ∀ {x y : A} {xs} →
                  xs ∷ʳ x ≡ y ∷ [] →
                  xs ≡ []
  ++-inj-lemma₂ {xs = xs} xs∷ʳx≡y∷[] = ∷ʳ-injectiveˡ xs [] xs∷ʳx≡y∷[]


  ++-inj-lemma₃ : ∀ (x₁ x₂ y₁ y₂ : A) xs →
                  xs ∷ʳ x₁ ∷ʳ x₂ ≡ y₁ ∷ y₂ ∷ [] →
                  x₁ ≡ y₁ × x₂ ≡ y₂
  ++-inj-lemma₃ x₁ x₂ y₁ y₂ xs fact = ∷ʳ-injectiveʳ xs [] lemma2 , lemma1
    where
      lemma1 : x₂ ≡ y₂
      lemma1 =  ∷ʳ-injectiveʳ (xs ++ x₁ ∷ []) (y₁ ∷ []) fact
      lemma2 : xs ∷ʳ x₁ ≡ [] ∷ʳ y₁
      lemma2 = ∷ʳ-injectiveˡ (xs ++ x₁ ∷ []) (y₁ ∷ []) fact



  head-tail-lemma : ∀ xs ys → hb-consistent (xs ++ ys) → ∃[ t ] (∃[ zs ] xs ≡ zs ++ [ t ]) → ∃[ t ] hb-consistent ([ t ] ++ ys)
  head-tail-lemma xs ys hb-xs++ys ∃t-zs = proof
    where
      proof = t , (hb-elimʳ zs ([ t ] ++ ys) (hb-cong hb-xs++ys (++-assoc2 xs ys zs t (cong (_++ ys) xs≡zs++[t]))))
        where
          t : Oper
          t = proj₁ ∃t-zs
          zs : List Oper
          zs = proj₁ (proj₂ ∃t-zs)
          xs≡zs++[t] : xs ≡ zs ++ [ t ]
          xs≡zs++[t] = proj₂ (proj₂ ∃t-zs)

  rev-lemma₁ : ∀ x y → x ≺* y → y *≻ x
  rev-lemma₁ x y (x-hb-y x≺y) = y-hb-x x≺y
  rev-lemma₁ x y (x-concurrent-y record { ¬x≺y = ¬x≺y ; ¬y≺x = ¬y≺x }) = x-concurrent-y (record { ¬x≺y = ¬x≺y ; ¬y≺x = ¬y≺x })



  head-lemma : ∀ (xs ys : List A) → xs ≢ [] → head (xs ++ ys) ≡ head xs
  head-lemma [] ys xs≢[] = ⊥-elim (xs≢[] refl)
  head-lemma (x ∷ xs) ys xs≢[] = refl


  hb-elimˡ : ∀ xs ys → hb-consistent (xs ++ ys) → hb-consistent xs
  hb-elimˡ [] ys hb-xs++ys = Linked.[]
  hb-elimˡ (x ∷ []) ys hb-xs++ys = [-]
  hb-elimˡ (x₁ ∷ x₂ ∷ xs) ys hb-xs++ys = just (linkedHead hb-xs++ys) ∷ᴸ hb-elimˡ (x₂ ∷ xs) ys (linkedTail hb-xs++ys)

 
  -- x happens before y or concurrent implies y doesn't happen before x
  [x≺y]or[x∥y]→¬y≺x : ∀ x y → x ≺ y ⊎ x ∥ y → ¬ y ≺ x
  [x≺y]or[x∥y]→¬y≺x x y (inj₁ x≺y) = asym x≺y
  [x≺y]or[x∥y]→¬y≺x x y (inj₂ x∥y) = ¬y≺x x∥y





  -- CRUCIAL PREFIX/SUFFIX LEMMA
  ∃-prefix-suffix : ∀ {y : A} xs ys →
                       y ∷ ys ↭ xs →
                       Distinct xs →
                       Distinct (y ∷ ys) →
                       ∃[ prefix ] (∃[ suffix ] xs ≡ suffix ++ y ∷ prefix)
  ∃-prefix-suffix [] ys y∷ys↭xs !xs !y∷ys = ⊥-elim (¬x∷xs↭[] y∷ys↭xs)
  ∃-prefix-suffix {y = y} (x ∷ []) ys y∷ys↭xs !xs !y∷ys = [] , ([] , proof)
    where
      lemma₁ : ∀{x y : A} ys → y ∷ ys ↭ x ∷ [] → ys ≡ []
      lemma₁ [] fact = refl
      lemma₁ (x ∷ ys) fact = ⊥-elim (bad↭ fact)

      lemma₂ : ∀{x y : A} ys → y ∷ ys ↭ x ∷ [] → y ≡ x
      lemma₂ [] fact = ∷-injectiveˡ (↭-singleton-inv fact)
      lemma₂ (x ∷ ys) fact = ⊥-elim (bad↭ fact)
      
      proof : x ∷ [] ≡ [] ++ y ∷ []
      proof = ↭-singleton-inv (↭-sym (subst₂ _↭_ (cong (y ∷_) (lemma₁ _ y∷ys↭xs)) refl y∷ys↭xs))

  ∃-prefix-suffix (x₁ ∷ x₂ ∷ xs) ys y∷ys↭xs !xs !y∷ys = {!!} , ({!!} , {!!})

  -- END CRUCIAL LEMMA






  -- Applies a list of operations to a starting state
  apply-ops : List Oper → State → Maybe State
  --apply-ops ops = foldl (_▷_) just (map interp ops)
  --apply-ops ops = foldr (_▷_) just (map interp ops)
  apply-ops ops = foldr (_◁_) just (map interp ops)
  
  apply-ops-[] : ∀ {s₀} → apply-ops [] s₀ ≡ just s₀
  apply-ops-[] = refl

  apply-ops-∷ : ∀ {y s₀} (xs : List Oper) → apply-ops (y ∷ xs) s₀ ≡ (⟨ y ⟩ ◁ (apply-ops xs)) s₀
  apply-ops-∷ [] = refl
  apply-ops-∷ (x ∷ xs) = refl


  --
  data _◁▷_ : Oper → Oper → Set where

    commute-ops : ∀{x y} →
                  x ∥ y →
                  (∀(s : State) → (⟨ x ⟩ ◁ ⟨ y ⟩) s ≡ (⟨ y ⟩ ◁ ⟨ x ⟩) s) →
                  x ◁▷ y

  concurrent-ops-commute : List Oper → Set
  concurrent-ops-commute xs = AllPairs _◁▷_ xs

  cc-ops-commute-∷⁻ : ∀ x xs →
                      concurrent-ops-commute (x ∷ xs) →
                      concurrent-ops-commute xs

  cc-ops-commute-∷⁻ x [] coc-x∷xs = AllPairs.[]
  cc-ops-commute-∷⁻ x (x₁ ∷ xs) (◁▷-holds AllPairs.∷ coc-x∷xs) = coc-x∷xs
  
  cc-ops-commute-++⁻ : ∀ xs ys →
                       concurrent-ops-commute (xs ++ ys) →
                       concurrent-ops-commute ys
  cc-ops-commute-++⁻ [] ys coc-xs++ys = coc-xs++ys
  cc-ops-commute-++⁻ (x ∷ xs) ys (◁▷holds AllPairs.∷ coc-xs++ys) = cc-ops-commute-++⁻ xs ys coc-xs++ys

  cc-ops-rearrange₁ : ∀ {x} xs ys →
                     concurrent-ops-commute (x ∷ xs ++ ys) →
                     concurrent-ops-commute (xs ++ x ∷ ys)
  cc-ops-rearrange₁ xs ys (◁▷-holds AllPairs.∷ coc-x∷xs++ys) = {!!}

  cc-ops-rearrange₂ : ∀ {x} xs ys →
                      concurrent-ops-commute (xs ++ x ∷ ys) →
                      concurrent-ops-commute (x ∷ xs ++ ys)
  cc-ops-rearrange₂ [] ys coc-xs++x∷ys = {!!}
  cc-ops-rearrange₂ (x ∷ xs) ys (◁▷-holds AllPairs.∷ coc-xs++x∷ys) = {!!}
  
  cc-ops-cc-set : ∀ x prefix suffix →
                  concurrent-ops-commute (x ∷ suffix ++ prefix) →
                  concurrent-set (x ∷ suffix) →
                  Distinct (x ∷ suffix ++ prefix) →
                  (∀(s : State) → apply-ops (suffix ++ x ∷ prefix) s ≡ apply-ops (x ∷ suffix ++ prefix) s)
  cc-ops-cc-set = ?      

  -- Bunch of Lemmas I don't have time to prove
  

  -- the BIG theorem
  convergence : ∀ xs ys →
                xs ↭ ys →
                concurrent-ops-commute xs →
                concurrent-ops-commute ys →
                Distinct xs →
                Distinct ys →
                (hb-xs : hb-consistent xs) →
                (hb-ys : hb-consistent ys) →
                (∀(s₀ : State) → apply-ops xs s₀ ≡ apply-ops ys s₀)
  convergence xs .[] xs↭ys cc-xs cc-ys !xs !ys hb-xs Linked.[] s₀ = cong₂ apply-ops (↭-empty-inv xs↭ys) refl
  convergence xs .(_ ∷ []) xs↭ys cc-xs cc-ys !xs !ys hb-xs [-] s₀ = cong₂ apply-ops (↭-singleton-inv xs↭ys) refl
  convergence xs (y₂ ∷ y₁ ∷ ys) xs↭ys cc-xs cc-ys !xs !ys hb-xs (y₂*≻y₁ Linked.∷ hb-y₁∷ys) s₀ =
    let found-prefix-suffix : ∃[ prefix ]( ∃[ suffix ] xs ≡ suffix ++ y₂ ∷ prefix )
        found-prefix-suffix = ∃-prefix-suffix xs (y₁ ∷ ys) (↭-sym xs↭ys) !xs !ys
        prefix = proj₁ found-prefix-suffix
        suffix = proj₁ (proj₂ found-prefix-suffix)
        xs≡suffix++y₂∷prefix = proj₂ (proj₂ found-prefix-suffix)

        fact₁ : concurrent-ops-commute (y₂ ∷ suffix ++ prefix)
        fact₁ = {!!}

        fact₂ : concurrent-set (y₂ ∷ suffix)
        fact₂ = {!!}

        fact₃ : Distinct (y₂ ∷ suffix ++ prefix)
        fact₃ = {!!}

        suf++pre↭y₁∷ys : suffix ++ prefix ↭ y₁ ∷ ys
        suf++pre↭y₁∷ys = {!!}
        
        lemma₁ : apply-ops xs s₀ ≡ apply-ops (suffix ++ y₂ ∷ prefix) s₀
        lemma₁ = cong₂ apply-ops xs≡suffix++y₂∷prefix refl

        lemma₂ : apply-ops (suffix ++ y₂ ∷ prefix) s₀ ≡ apply-ops (y₂ ∷ suffix ++ prefix) s₀
        lemma₂ = cc-ops-cc-set y₂ prefix suffix fact₁ fact₂ fact₃ s₀
           
        l₁ : concurrent-ops-commute (suffix ++ prefix)
        l₁ = cc-ops-commute-∷⁻ y₂ (suffix ++ prefix) fact₁

        l₂ : concurrent-ops-commute (y₁ ∷ ys)
        l₂ = cc-ops-commute-∷⁻ y₂ (y₁ ∷ ys) cc-ys
        
        l₃ : Distinct (suffix ++ prefix)
        l₃ = {!!}

        l₄ : Distinct (y₁ ∷ ys)
        l₄ = {!!}

        l₅ : hb-consistent (suffix ++ prefix)
        l₅ = {!!}
        
        l₆ : hb-consistent (y₁ ∷ ys)
        l₆ = hb-head-elim ((y₂*≻y₁ Linked.∷ hb-y₁∷ys))

        ind-hyp : ∀ s → apply-ops (suffix ++ prefix) s ≡ apply-ops (y₁ ∷ ys) s
        ind-hyp s = convergence (suffix ++ prefix) (y₁ ∷ ys) suf++pre↭y₁∷ys l₁ l₂ l₃ l₄ l₅ l₆ s
            

        ind-step : (⟨ y₂ ⟩ ◁ (apply-ops (suffix ++ prefix))) s₀ ≡ (⟨ y₂ ⟩ ◁ (apply-ops (y₁ ∷ ys))) s₀
        ind-step = cong₂ (λ y r → r >>= λ z → ⟨ y ⟩ z) refl (ind-hyp s₀)
      in
        begin
          apply-ops xs s₀                              ≡⟨ lemma₁ ⟩
          apply-ops (suffix ++ y₂ ∷ prefix) s₀         ≡⟨ lemma₂ ⟩
          apply-ops (y₂ ∷ suffix ++ prefix) s₀         ≡⟨ refl ⟩
          (⟨ y₂ ⟩ ◁ (apply-ops (suffix ++ prefix))) s₀ ≡⟨ ind-step ⟩
          (⟨ y₂ ⟩ ◁ (apply-ops (y₁ ∷ ys))) s₀          ≡⟨ refl ⟩
          apply-ops (y₂ ∷ y₁ ∷ ys) s₀
        ∎
     





  -- Represents the proposition that a data structure
  -- is strongly eventually consistent
  record IsSEC (op-history : List Oper → Set)
               (init-state : State)
               : Set where

    field
      causality : ∀ xs → op-history xs → hb-consistent xs
      distinctness : ∀ xs → op-history xs → Distinct xs
      trunc-history : ∀ x xs → op-history (x ∷ xs) → op-history xs
      commutativity : ∀ xs → op-history xs → concurrent-ops-commute xs
      no-failure : ∀ x xs state →
                   op-history (x ∷ xs) →
                   apply-ops xs init-state ≡ just state →
                   ⟨ x ⟩ state ≢ nothing
  
