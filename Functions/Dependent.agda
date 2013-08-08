--http://people.inf.elte.hu/divip/AgdaTutorial/Functions.Dependent.html

module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero  -- Note: different zeros
fromℕ (suc n) = suc (fromℕ n)

--Define a substraction with restricted domain:
_-_ : (n : ℕ) → Fin (suc n) → ℕ
n - zero = n
(suc n) - (suc m) = n - m
--0 - zero = 0
-- TODO: do I need to prove the contrediction of 0 - _ ?
0 - _ = 0

------------------
toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (suc( n )) = suc( toℕ(n))

-- TODO: Exercise: Define fromℕ≤ such that toℕ (fromℕ≤ e) is m if e : m < n:
--fromℕ≤ : ∀ {m n} → m < n → Fin n

-- ...

-- Exercise: Define four such that toℕ four is 4:
four : Fin 66
four = suc( suc (suc (suc zero))) --TODO: this is what he meant right?

-- TODO: Exercise: Define raise such that toℕ (raise n i) is the same as n + toℕ i:
--raise : ∀ {m} n → Fin m → Fin (n + m)


-- Exercise: Define head and tail.
head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (x ∷ _) = x


tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

-- Exercise: Define concatenation for vectors.
_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys) --TODO: review the magic, how does it know these are added?

-- Exercise: Define maps. (Note that two cases will be enough!)
maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] [] = []
maps (f ∷ fs) (y ∷ ys) = (f y) ∷ (maps fs ys)

-- TODO: Exercise: Define replicate.
--replicate : ∀ {n}{A : Set} → A → Vec A n --TODO: really not sure?
--replicate 0 _ = []
--replicate (suc n) a = a ∷ (replicate n a)

-- ...
