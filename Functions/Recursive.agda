module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_

-- Exercise: Define pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
pred  : ℕ → ℕ      -- predecessor (pred 0 = 0)
pred zero = zero
pred (suc m) = m

infixl 6 _∸_
_∸_   : ℕ → ℕ → ℕ  -- subtraction (0 ∸ n = n)
0 ∸ n = n
suc m ∸ n = suc n

infixl 7 _*_
_*_   : ℕ → ℕ → ℕ  -- multiplication
0 * n = 0
suc m * n = (m * n) + n

infixl 6 _⊔_
_⊔_   : ℕ → ℕ → ℕ  -- maximum
0 ⊔ n = n
n ⊔ 0 = n
suc n ⊔ suc m = suc (n ⊔ m)

infixl 7 _⊓_
_⊓_   : ℕ → ℕ → ℕ  -- minimum
0 ⊓ _ = 0
_ ⊓ 0 = 0
suc n ⊓ suc m = suc (n ⊓ m)

⌊_/2⌋ : ℕ → ℕ      -- half (⌊ 1 /2⌋ = 0)
⌊ 0 /2⌋ = 0
⌊ 1 /2⌋ = 0
⌊ (suc (suc n)) /2⌋ = suc ( ⌊ n /2⌋ )

odd   : ℕ → Bool   -- is odd
odd 0 = false
odd 1 = true
odd (suc (suc n)) = odd n

--even  : ℕ → Bool   -- is even
--even n = not (odd n)
--boring...


-- Exercise: Define even and odd mutually with the mutual keyword!
---TODO: WTF is the mutual keyword?

_≡?_  : ℕ → ℕ → Bool  -- is equal
0 ≡? 0 = true
suc n ≡? suc m = n ≡? m
_ ≡? _ = false

_≤?_  : ℕ → ℕ → Bool  -- is less than or equal
0 ≤? _ = true
suc n ≤? suc m = n ≤? m
_ ≤? _ = false

open import Sets.Recursive using (ℕ⁺; one; double; double+1; ℕ₂; zero; id)

--Exercise: define the conversion function:
--from : ℕ₂ → ℕ  -- hint: use _*_
--from zero = 0
--from  = 0

--TODO: the rest of the the things
