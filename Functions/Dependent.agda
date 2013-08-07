module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero  -- Note: different zeros
fromℕ (suc n) = suc (fromℕ n)

--E:
_-_ : (n : ℕ) → Fin (suc n) → ℕ
n - zero = n
(suc n) - (suc m) = n - m
--0 - zero = 0
-- do I need to prove the contrediction of 0 - _ ?
0 - _ = 0
