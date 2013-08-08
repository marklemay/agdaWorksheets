module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

--Exercise:  Define two functions which define the isomorphism between List ⊤ and ℕ!

fromList : List ⊤ → ℕ
fromList [] = 0
fromList ( _ ∷ xs) = suc ( fromList xs)

toList   : ℕ → List ⊤
toList 0 = []
toList (suc x) = tt ∷ (toList x)

--TODO other excercise

--Exercise: Define the following functions on lists:

map  : {A B : Set} → (A → B)      → List A → List B -- regular map
map _ [] = []
(map f) ( x ∷ xs) = (f x) ∷ ((map f) xs)

--TODO: is this enough t go on?
--maps : {A B : Set} → List (A → B) → List A → List B -- pairwise map

--Exercise: Define the singleton list function:
[_] : {A : Set} → A → List A
[ x ] = x ∷ []

id : {A : Set} → A → A
id a = a

aNumber = id {ℕ} (suc zero)

--Exercise: Define const : {A B : Set} → A → B → A!
const : {A B : Set} → A → B → A
const a _ = a

--Exercise: Define flip : {A B C : Set} → (A → B → C) → B → A → C!
flip : {A B C : Set} → (A → B → C) → B → A → C
flip fab b a = fab a b

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

--Exercise: Define a function which swaps the two elements!
swap : {A B : Set} → A × B → B × A
swap (a , b) = b , a

--Exercise: 
proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

--Exercise: Define a function which swaps the two elements!
--TODO:  this is fucking impossible right?

--Exercise: Define the eliminator function for disjoint union:
[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[ ac , bc ] (inj₁ a) = ac a
[ ac , bc ] (inj₂ b) = bc b
