module Functions.Universal_Quantification where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s; _≤′_; ≤′-step; ≤′-refl)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (flip; _$_; _∘_)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

-- Exercises: Define the following functions (prove these properties):
≤-trans      : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans  z≤n  _ = z≤n
≤-trans (s≤s x) (s≤s y) = s≤s (≤-trans x y) 
--TODO: why do I not need the case
--≤-trans _ z≤n

--TODO: use the called out version
[_,_]' : {A B AC BC : Set} → (A → AC) → (B → BC) → (A ⊎ B → AC ⊎ BC)
[ ac , bc ]' (inj₁ a) = inj₁ (ac a)
[ ac , bc ]' (inj₂ b) = inj₂ (bc b)

total        : ∀ m n → m ≤ n ⊎ n ≤ m -- hint: use [_,_]′
total 0 _ = (inj₁ z≤n )
total _ 0 = (inj₂ z≤n )
total (suc x) (suc y) = [ s≤s , s≤s ]' (total x y) -- FUCK YEAH!!!!

-- "From the 4 above properties follows that _≤_ is a total order on ℕ. (We can look at _≤_ as a relation over ℕ.)"
--TODO: I'm no expert, but that looks like 3 properties to me

≤-pred  : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred (s≤s z≤n) = z≤n
≤-pred (s≤s x) = x

--scrathch

≤-mono'  : ∀ m n k → n ≤ m → k + n ≤ k + m
≤-mono' _ _ 0 p = p
≤-mono' a b (suc x) p = s≤s (≤-mono' a b x p)

--TODO: how do I get at the k?
--≤-mono  : ∀ {m n k} → n ≤ m → k + n ≤ k + m
--≤-mono p = p

-- Exercises: Define the following functions:
≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n = z≤n
≤-step (s≤s p) = (s≤s (≤-step p))

--TODO: too hard without middle click lookup

--≤′⇒≤ : ∀ {a b} → a ≤′ b → a ≤ b


--z≤′n : ∀ n → zero ≤′ n


--s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n


--≤⇒≤′ : ∀ {a b} → a ≤ b → a ≤′ b

--Define fin≤:


--fin≤ : ∀ {n}(m : Fin n) → toℕ m < n