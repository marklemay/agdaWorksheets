module  Sets.Enumerated where

data Bool : Set where
  true  : Bool
  false : Bool

data Bool' : Set where
  true' false'  : Bool'


data ⊥ : Set where   -- There is no constructor.


data ⊤ : Set where
  tt : ⊤

data name : Set where
  elem₁ elem₂ : name
