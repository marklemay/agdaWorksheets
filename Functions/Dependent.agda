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
0 - (suc ())

-- Define toℕ:
toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (suc( n )) = suc( toℕ(n))

-- Exercise: TODO: Define fromℕ≤ such that toℕ (fromℕ≤ e) is m if e : m < n
--really define a functoin that return m as the finite set of n
--fromℕ≤ : ∀ {m n} → m < n → Fin n
--fromℕ≤ (0 < _) = zero
--fromℕ≤ ((suc x) < (suc y)) = suc fromℕ≤ (x < y)

--scratch
inject+' : ∀ { m } → Fin  m → Fin (m + 0)
inject+' zero = zero
inject+' (suc x) = suc (inject+' x)

inject+'' : ∀ {m} → Fin m → Fin (m + 2)
inject+'' zero = zero
inject+'' (suc x) = suc (inject+'' x)

-- Exercise: TODO: Define inject+ such that toℕ (inject+ n i) is the same as toℕ i:
--inject+ : ∀ {m} n → Fin m → Fin (m + n)
--inject+ (suc m) zero = zero {m}
--inject+ m (suc x) = suc {m} (inject+ 0 x)
--inject+ (suc x) y = suc ()

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
--replicate : ∀ {n}{A : Set} → A → Vec A n --TODO: really not sure? how do you tell it how many times to replicate?
--replicate _ = []
--replicate 0 _ = []
--replicate (suc n) a = a ∷ (replicate n a)

-- TODO: Exercise: Define map with the help of maps and replicate.
-- map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n

-- TODO: Exercise: Define zip with the help of map and maps.
--zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n


-- Exercise: Define safe element indexing.
_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
(x ∷ _) ! zero = x
(_ ∷ xs) ! (suc n) = xs ! n
[] ! () --LIKE A BOSS!