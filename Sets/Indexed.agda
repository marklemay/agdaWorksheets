-- http://people.inf.elte.hu/divip/AgdaTutorial/Sets.Indexed.html

module Sets.Indexed where

open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

-- TODO: Exercise: Define a Bool indexed family of sets such that the set indexed by false contains no elements and the set indexed by true contains one element!

data Solution : Bool → Set where
  s :  Solution true

-- Exercise: Define a ℕ indexed family of sets such that the sets indexed by even numbers contain one element and the others are empty!
data Fin1 : ℕ → Set where
  zerox : Fin1 0
  sucx  : (n : ℕ) → Fin1 n → Fin1 (suc (suc n))

-- scratch:
ex : Fin1 0
ex = zerox

exx : Fin1 2
exx = sucx 0 zerox

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

-- Exercise: TODO: Define a Bool indexed family of sets with two parameters, A and B, such that the set indexed by false contains an A element and the set indexed by true contains a B element!


