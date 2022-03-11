module Utils.Arrow where


open import Data.Maybe using (Maybe; just; nothing; _>>=_)


infix 4 _▷_
infixr 4 _◁_
_▷_ : ∀{A : Set} → (A → Maybe A) → (A → Maybe A) → (A → Maybe A)
f ▷ g = λ x → f x >>= λ y → g y

_◁_ : ∀{A : Set} → (A → Maybe A) → (A → Maybe A) → (A → Maybe A)
g ◁ f = λ x → f x >>= λ y → g y
