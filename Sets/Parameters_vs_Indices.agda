-- http://people.inf.elte.hu/divip/AgdaTutorial/Sets.Parameters_vs_Indices.html#1
module Sets.Parameters_vs_Indices where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)

--TODO: remove this and call out to prevous worksheet instead{{{
data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k
--}}}TODO: remove this and call out to prevous worksheet instead


--data _≤′_ : ℕ → ℕ → Set where
--  ≤′-refl : {m : ℕ} →                       m ≤′ m
--  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

data _≤′_ (m : ℕ) : ℕ → Set where
  ≤′-refl :                       m ≤′ m
  ≤′-step : {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

--data _≤″_ : ℕ → ℕ → Set where
--  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

--data _≤″_ (m : ℕ) : ℕ → Set where
--  ≤+ : ∀ {n k} → m + n ≡ k → m ≤″ k

data _≤″_ (m : ℕ) (k : ℕ) : Set where
  ≤+ : ∀ {n} → m + n ≡ k → m ≤″ k

data 10≤′ : ℕ → Set where
  10≤′-refl :                       10≤′ 10
  10≤′-step : {n : ℕ} →  10≤′ n  →  10≤′(suc n)  --TODO let him know that it needs to be "(suc n)" instead of "suc n"

data  _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_

data _∈_ {A : Set}(x : A) : List A → Set where
  first : ∀ {xs} → x ∈ x ∷ xs
  later : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

infix 4 _∈_

-- Excercise: Define _⊆_ {A : Set} : List A → List A → Set!
--TODO: is it ok that there are no paramiters?
--TODO: this still needs some work
data _⊆_ {A : Set} : List A → List A → Set where
  first⊆ : ∀ {xs} → [] ⊆ xs
  later⊆ : ∀ {xs ys x} → x ∈ ys → xs ⊆ ys → x ∷ xs ⊆ ys

infix 4 _⊆_

--scratch:
1∈123 : 1 ∈ 1 ∷ 2 ∷ 3 ∷ []
1∈123 = first

2∈123 : 2 ∈ 1 ∷ 2 ∷ 3 ∷ []
2∈123 = later first

[]⊆123 : [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
[]⊆123 = first⊆

2⊆123 : 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
2⊆123 = (first⊆ 2∈123) []⊆123

-- Excercise: Prove that 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []!
solution12⊆123 : 1 ∷ 2 ∷ [] ⊆ 1 ∷ 2 ∷ 3 ∷ []
solution12⊆123 = (later⊆ 1∈123) ((later⊆ 2∈123) first⊆)
