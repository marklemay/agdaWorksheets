module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)


data _≡_ {A : Set} (x : A) : A → Set  where
  refl : x ≡ x

infix 4 _≡_


refl'  : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym   : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl   -- after pattern matching on 'refl', 'a' and 'b' coincides

--Exercise:
trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl -- sure that works, why not

--Exercise: Prove that every function is compatible with the equivalence relation (congruency):
cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong _ refl = refl --uhhh....

1+1≡2 : 1 + 1 ≡ 2
1+1≡2 = refl


+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero    = refl --trivial equality
+-right-identity (suc n) = cong suc (+-right-identity n)
--+-right-identity _ = refl

--Exercise: Finish the ingredients of the proof that (ℕ, _+_) is a commutative monoid!
+-left-identity  : ∀ a → 0 + a ≡ a
+-left-identity _ = refl


stall : ∀ n → ℕ
stall 0 = 0
stall 5 = 5
stall x = stall (suc x)


--TODO:
--+-assoc          : ∀ a b c → a + (b + c) ≡ (a + b) + c -- hint: use cong
--+-assoc 0 0 0 = refl
--+-assoc (suc a) b c = cong suc (+-assoc a b c)
--+-assoc a (suc b) c = cong suc (+-assoc a b c)
--+-assoc a b (suc c) = cong suc (+-assoc a b c)


--TODO:
--m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
--m+1+n≡1+m+n 0 0 = refl


fromList : List ⊤ → ℕ
fromList [] = zero
fromList (x ∷ xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList zero = []
toList (suc n) = tt ∷ toList n

-- TODO: ...