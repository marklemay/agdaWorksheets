module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)

not : Bool → Bool
not true  = false
not false = true

_∧_   : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_

--Exercise: Define logical OR:
infixr 5 _∨_
 
_∨_   : Bool → Bool → Bool
false ∨ false = false
_ ∨ _ = true

--Exercise: Define logical OR with one alternative, with the help of not and _∧_!

_∨'_   : Bool → Bool → Bool
x ∨' y = not( not(x) ∧ not(y))

--logic bitches!

--Exercise: Define a set named Answer with three elements, yes, no and maybe.

data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer

--Exercise: Define logical operations on Answer!

not' : Answer → Answer
not' yes  = no
not' no = yes
not' maybe = maybe

_∧'_   : Answer → Answer → Answer
yes  ∧' x = x
x ∧' yes = x
no ∧' _ = no
_ ∧' no = no
maybe ∧' maybe = maybe

--... boring

--Exercise: Define a set named Quarter with four elements, east, west, north and south.
data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter

--... boring

