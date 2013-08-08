module Sets.Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

data Fin1 : ℕ → Set where
  zerox : Fin1 0
  sucx  : (n : ℕ) → Fin1 n → Fin1 (suc (suc n))

ex : Fin1 0
ex = zerox

exx : Fin1 2
exx = sucx 0 zerox

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)
