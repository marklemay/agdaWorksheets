--http://people.inf.elte.hu/divip/AgdaTutorial/Sets.Propositions.html#1

module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Excersise: Construct one proof for each proposition if possible:

e1 : ⊤ × ⊤
e1 = tt , tt

-- e2 : ⊤ × ⊥
-- no proof exists

-- e3 : ⊥ × ⊥
-- no proof exists

e4 : ⊤ ⊎ ⊤
e4 = inj₁ tt

e5 : ⊤ ⊎ ⊥
e5 = inj₁ tt

-- e6 : ⊥ ⊎ ⊥
-- no proof exists

test :  ⊥ ⊎ ⊤ ⊎ ⊥
test =  inj₂ (inj₁ tt)

e7 : ⊥ ⊎ ⊤ ⊎ ⊤ × (⊥ ⊎ ⊥) ⊎ ⊤
-- × is lower precidence then ⊎
e7 = inj₂ (inj₁ tt)

data  _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤ n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤ suc n
--  4≤2 : 4 ≤ 2 --pattern matching 

infix 4 _≤_

0≤1 : 1 ≤ 10
0≤1 = s≤s z≤n

-- Excersise: Prove that 3 ≤ 7!
3≤7 : 3 ≤ 7
3≤7 = s≤s (s≤s (s≤s z≤n))

7≰3 : 7 ≤ 3 → ⊥
7≰3 (s≤s (s≤s (s≤s ())))

-- Excersise,  there is something going on syntacticly that I just don't get, where's the where?
-- "how are you assuered this cannot be constructed by other means."
4≰2 : 4 ≤ 2 → ⊥
4≰2 (s≤s (s≤s ())) -- "this is a form of pattern matching, adding constructors prevents this from typechecking"

8≰4 : 8 ≤ 4 → ⊥
8≰4 (s≤s x) = 7≰3 x

-- Excersise: Define an indexed set _isDoubleOf_ : ℕ → ℕ → Set such that m isDoubleOf n is non-empty iff m is the double of n!
data _isDoubleOf_ : ℕ → ℕ → Set where
  zisDoubleOfz : zero isDoubleOf zero
  ssisDoubleOfs : {m : ℕ} → {n : ℕ} →   m isDoubleOf n  →  suc (suc m) isDoubleOf suc n

infix 4 _isDoubleOf_

-- scratch:
0D0 : 0 isDoubleOf 0
0D0 = zisDoubleOfz

2D1 : 2 isDoubleOf 1
2D1 = ssisDoubleOfs zisDoubleOfz

-- exercise: Prove that 8 isDoubleOf 4 is non-empty!
8isDoubleOf4 : 8 isDoubleOf 4
8isDoubleOf4 = ssisDoubleOfs (ssisDoubleOfs (ssisDoubleOfs (ssisDoubleOfs zisDoubleOfz)))

-- exercise: Prove that 9 isDoubleOf 4 is empty!
9isDoubleOf4 : 9 isDoubleOf 4 → ⊥
9isDoubleOf4 (ssisDoubleOfs (ssisDoubleOfs (ssisDoubleOfs (ssisDoubleOfs () ))))

-- excersise: Define an indexed set Odd : ℕ → Set such that odd n is non-empty iff n is odd! 
data Odd : ℕ → Set where
  odd1 : Odd 1
  oddss : {n : ℕ} → Odd n → Odd (suc (suc n))

--scratch:
o3 : Odd 3
o3 = oddss odd1

-- exercise: Prove that Odd 9 is non-empty!
o9 : Odd 9
o9 = oddss (oddss (oddss (oddss odd1)))

-- exercise: Prove that Odd 8 is empty!
o8 : Odd 8 → ⊥
o8 (oddss (oddss (oddss (oddss ()))))

-- exercise: Define Even : ℕ → Set and Odd : ℕ → Set mutually!
data Even' : ℕ → Set
data Odd' : ℕ → Set

data Even' where
  z  : Even' 0
  evens :  {n : ℕ} → Odd' n → Even' (suc n)

data Odd' where
  odds : {n : ℕ} → Even' n → Odd' (suc n)

-- scratch:
even'4 : Even' 4
even'4 = evens (odds (evens (odds z)))

odd'4 : Odd' 4 → ⊥
odd'4 (odds (evens (odds (evens ()))))

-- exercise: Define equality _≡_ : ℕ → ℕ → Set!
data _≡_ : ℕ → ℕ → Set where
  z≡z : zero ≡ zero
  s≡s : {m : ℕ} → {n : ℕ} →   m ≡ n  →  suc m ≡ suc n

infix 4 _≡_

-- scratch: 

e00 : 0 ≡ 0
e00 = z≡z

-- why won't the following work?
-- Answer: it thinks it's a floating point
-- 0e0 : 0 ≡ 0
-- 0e0 = z≡z

e22 : 2 ≡ 2
e22 = s≡s (s≡s z≡z)

e12 : 1 ≡ 2 → ⊥
e12 (s≡s ())

-- exercise: Define non-equality _≠_ : ℕ → ℕ → Set!
-- TODO: is there a better answer?
data _≠_ : ℕ → ℕ → Set where
  z≠o : 0 ≠ 1
  z≠s : {n : ℕ} →   0 ≠ n  →  0 ≠ suc n
  o≠z : 1 ≠ 0
  s≠z : {n : ℕ} →   n ≠ 0  →  suc n ≠ 0
  s≠s : {m : ℕ} → {n : ℕ} →   m ≠ n  →  suc m ≠ suc n

infix 4 _≠_

-- scratch

ne01 : 0 ≠ 2
ne01 = z≠s z≠o

ne24 : 2 ≠ 4
ne24 = s≠s (s≠s (z≠s z≠o))

ne22 : 2 ≠ 2 → ⊥
ne22 (s≠s (s≠s ()))


data _≤′_ : ℕ → ℕ → Set where
  ≤′-refl : {m : ℕ} →                       m ≤′ m
  ≤′-step : {m : ℕ} → {n : ℕ} →  m ≤′ n  →  m ≤′ suc n

infix 4 _≤′_

-- Syntactic abbreviations

data  _≤0_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                       zero  ≤0 n
  s≤s : {m : ℕ} → {n : ℕ} →   m ≤ n  →  suc m ≤0 suc n

--The arrows between typed variables are not needed (also in case of round parenthesis):


data  _≤1_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →                     zero  ≤1 n
  s≤s : {m : ℕ} {n : ℕ} →   m ≤1 n  →  suc m ≤1 suc n

--Typed variables with the same type can be contracted (also in case of round parenthesis):

data  _≤2_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} →               zero  ≤2 n
  s≤s : {m n : ℕ} →   m ≤2 n  →  suc m ≤2 suc n

--Inferable expressions can be replaced by an underscore:

data  _≤3_ : ℕ → ℕ → Set where
  z≤n : {n : _} →               zero  ≤3 n
  s≤s : {m n : _} →   m ≤3 n  →  suc m ≤3 suc n

--Variables with inferred types can be introduced by ∀:

data  _≤4_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} →               zero  ≤4 n
  s≤s : ∀ {m n} →   m ≤4 n  →  suc m ≤4 suc n

-- Lets add some fucking numbers
data _+_≡_ : ℕ → ℕ → ℕ → Set where
  znn : ∀ {n} → zero + n ≡ n
  sns : ∀ {m n k} → m + n ≡ k → suc m + n ≡ suc k

--scratch
add1p2e3 : 1 + 2 ≡ 3
add1p2e3 = sns znn 

add1p2e4 :  1 + 2 ≡ 4 → ⊥
add1p2e4 ( sns ())

-- exercise: Prove that 5 + 5 = 10!
add5p5e10 : 5 + 5 ≡ 10
add5p5e10 = sns (sns (sns (sns (sns znn))))

-- exercise: Prove that 2 + 2 ≠ 5!
add2p2e5 : 2 + 2 ≡ 5 → ⊥
add2p2e5 (sns (sns ()))

-- exercise: Define _⊓_ : ℕ → ℕ → Set such that n ⊓ m ≡ k iff k is the minimum of n and m! 
-- TODO: I think this is a little bit ambigous.  souldn't it be _⊓_≡_ : ℕ → ℕ  → ℕ → Set like how the inhabited set of additions was defined.
-- TODO: I will assume it works my way, TODO: check in on the mailing list
data _⊓_≡_ : ℕ → ℕ → ℕ → Set where
  z⊓s : ∀ {n} → 0 ⊓ n ≡ 0
  s⊓z : ∀ {n} → n ⊓ 0 ≡ 0
  s⊓s : ∀ {n m k} → n ⊓ m ≡ k → suc n ⊓ suc m ≡ suc k

-- exercise: Prove that 3 ⊓ 5 ≡ 3 is non-empty!
min35 : 3 ⊓ 5 ≡ 3
min35 = s⊓s (s⊓s (s⊓s z⊓s))

-- exercise: Prove that 3 ⊓ 5 ≡ 5 is empty!
min355 : 3 ⊓ 5 ≡ 5 → ⊥
min355 (s⊓s (s⊓s (s⊓s ())))

-- exercise: Define _⊔_ : ℕ → ℕ → Set such that n ⊔ m ≡ k iff k is the maximum of n and m! 
-- TODO: same reservations as before
data _⊔_≡_ : ℕ → ℕ → ℕ → Set where
  z⊔s : ∀ {n} → 0 ⊔ n ≡ n
  s⊔z : ∀ {n} → n ⊔ 0 ≡ n
  s⊔s : ∀ {n m k} → n ⊔ m ≡ k → suc n ⊔ suc m ≡ suc k

-- exercise: Prove that 3 ⊔ 5 ≡ 5 is non-empty!
max355 : 3 ⊔ 5 ≡ 5
max355 = s⊔s (s⊔s (s⊔s z⊔s))

-- exercise: Prove that 3 ⊔ 5 ≡ 3 is empty!
max353 : 3 ⊔ 5 ≡ 3 → ⊥
max353 (s⊔s (s⊔s (s⊔s ())))


data _≤″_ : ℕ → ℕ → Set where
  ≤+ : ∀ {m n k} → m + n ≡ k → m ≤″ k

-- exercise: Define _isDoubleOf_ : ℕ → ℕ → Set on top of _+_≡_! 
data _isDoubleOf'_ : ℕ → ℕ → Set where
  npnem : ∀ {n m} → n + n ≡ m → m isDoubleOf' n

-- exercise: Prove that 8 isDoubleOf 4 is non-empty!
d84 : 8 isDoubleOf' 4
d84 = npnem (sns (sns (sns (sns znn))))

-- exercise: Prove that 9 isDoubleOf 4 is empty!
d94 : 9 isDoubleOf' 4 → ⊥
d94 (npnem (sns (sns (sns (sns  ())))))

-- exercise: Define _*_≡_ : ℕ → ℕ → Set with the help of _+_≡_!
data _*_≡_ : ℕ → ℕ → ℕ → Set where
  base : ∀ {n} → 0 * n ≡ 0
  succ : ∀ {n m k j} → m * n ≡ j → j + n ≡ k → suc m * n ≡ k

-- scratch
m900 : 0 * 9 ≡ 0
m900 = base

--add1p2e3 : 1 + 2 ≡ 3 --already defined
--add1p2e3 = sns znn

m911 : 1 * 9 ≡ 9
m911 = (succ base) znn

1*3≡3 : 1 * 3 ≡ 3
1*3≡3 = succ base znn

3+3≡6 : 3 + 3 ≡ 6
3+3≡6 = sns (sns (sns znn))

2*3≡6 : 2 * 3 ≡ 6
2*3≡6 = (succ 1*3≡3) 3+3≡6

6+3≡9 : 6 + 3 ≡ 9
6+3≡9 = sns (sns (sns (sns (sns (sns znn)))))

5+3≡8 : 5 + 3 ≡ 8
5+3≡8 = sns (sns (sns (sns (sns znn))))

2+3≡8 : 2 + 3 ≡ 5
2+3≡8 =  sns (sns znn)

m132 : 1 * 3 ≡ 2 → ⊥
m132 ((succ base) ())

3+3≡5 : 3 + 3 ≡ 5 → ⊥
3+3≡5 (sns (sns (sns ())))

m235 : 2 * 3 ≡ 5 → ⊥
m235 ( ( succ  (succ base znn) ) x ) = 3+3≡5 x
--TODO: why won't this work?
--m235 ( ( succ  (1*3≡3) ) x ) = 3+3≡5 x

m1*1≡10 : 1 * 1 ≡ 10 → ⊥
m1*1≡10 ((succ base) ())

1+9≡10 : 1 + 9 ≡ 10
1+9≡10 =  sns znn

0+9≡9 : 0 + 9 ≡ 9
0+9≡9 = znn

0+1≡10 : 0 + 1 ≡ 10 → ⊥
0+1≡10 ()

---TODO: why won't this work
m2*1≡10 : 1 * 1 ≡ 10 → ⊥
m2*1≡10 (succ base y) = 0+1≡10 y

-- exercise: Prove that 3 * 3 ≡ 9 is non-empty!
m339 : 3 * 3 ≡ 9
m339 = succ ((succ 1*3≡3) 3+3≡6) 6+3≡9

-- Exercise: Prove that 3 * 3 ≡ 8 is empty!
m338 : 3 * 3 ≡ 8 → ⊥
m338 (succ (succ (succ base znn) (sns (sns (sns znn)))) (sns (sns (sns (sns (sns (sns ())))))))
--m338 (succ (2*3=5) 5+3≡8)
--m338 (succ ((succ 1*3=2) 2+3≡5) 5+3≡8)
--m338 (succ ((succ ((succ base) znn)) 2+3≡5) 5+3≡8)

-- TODO: call out to worksheet like a pro{{{
data ℕ⁺ : Set where
  one      :      ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺
--}}}TODO: call out to worksheet like a pro

-- Exercise: Define _≈_ : ℕ → ℕ⁺ → Set which represents the (canonical) isomorphism between ℕ and ℕ⁺!*
data _≈_ : ℕ → ℕ⁺ → Set where
 -- there is no mapping from 0, TODO: is that right?  THIS MAKES IT NOT AN ISOMORPHISM
 1≈1 : 1 ≈ one
 double : ∀ {m n b} →   m isDoubleOf n  → n ≈ b → m ≈ (double b)
 double+1 : ∀ {m n b} →   m isDoubleOf n  → n ≈ b → (suc m) ≈ (double+1 b)
--TODO: is there a way to do this that doesn't need such redundant proofs of doubpleing?

2≈2 : 2 ≈ (double one) 
2≈2 = double (ssisDoubleOfs zisDoubleOfz) 1≈1

3≈3 : 3 ≈ (double+1 one) 
3≈3 = double+1 (ssisDoubleOfs zisDoubleOfz) 1≈1

4≈4 : 4 ≈ (double (double one)) 
4≈4 = double (ssisDoubleOfs (ssisDoubleOfs zisDoubleOfz)) 2≈2

-- Exercise: Prove that 5 ≈ double+1 (double one) is non-empty!
5≈5 :  5 ≈ double+1 (double one)
5≈5 = double+1 (ssisDoubleOfs (ssisDoubleOfs zisDoubleOfz)) 2≈2

-- Exercise: Prove that 4 ≈ double+1 (double one) is empty!
4≈5 : 4 ≈ (double+1 (double one)) → ⊥
4≈5 (double+1 (ssisDoubleOfs ()) (double _ 1≈1))  --  really liking the use of underscore right here