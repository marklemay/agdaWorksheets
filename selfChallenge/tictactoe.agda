module tictactoe where
open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe

--data Board

data GS : ℕ -> Set where 
 s : GS 0
 n : ( n : ℕ ) -> GS n -> GS (suc n)

add2 : ℕ -> ℕ
add2 w = suc (suc w )

data Player : Set where
 x : Player
 o : Player

data Square : Set where
 - : Square
 x : Square
 o : Square

--TODO: alias Vec Square 9 to Bourd for easy reading

--Somthing nice would make this an implicit converion
player2Square : Player -> Square
player2Square x = x
player2Square o = o 


-- TODO: make replace safe with finite and such
replace : {len : ℕ}{A : Set} -> A -> ℕ -> Vec A len -> Vec A len
replace _ _ [] = []
replace a 0 ( _ ∷ xs ) = a ∷ xs
replace a (suc nn) ( xx  ∷ xs ) = xx ∷ (replace a nn xs)

--lookup, TODO: make fin safe on input or better yet use std lib
lookup : {len : ℕ}{A : Set} -> ℕ -> Vec A len -> Maybe A
lookup 0 ( xx  ∷ xs ) = just xx
lookup (suc nn) ( xx  ∷ xs ) = lookup nn xs
lookup _ _ = nothing

--TODO: make move safe?
--TODO: prove some assumption on move, at most one thing is changed, exactly one thing is changed
move : Player -> ℕ -> Vec Square 9 -> (Vec Square 9)
move p nn bb with lookup nn bb
... | just - =  (replace (player2Square p) nn bb )
... | _ = bb
--move _ _ _ = nothing

-- ( - ∷ - ∷ - ∷
--         - ∷ - ∷ - ∷
--         - ∷ - ∷ - ∷ [] )

-- lookup
-- replace?

data GS' : Vec ℕ 1 -> Set where 
 s : GS' ( (add2 69) ∷ [] )
-- n : ( n : ℕ ) -> GS' n -> GS' (suc n)

data GameState : Player -> Vec Square 9 -> Set where
 start : GameState x ( - ∷ - ∷ - ∷
                     - ∷ - ∷ - ∷
                     - ∷ - ∷ - ∷ [] )
 xturn : (n : ℕ) -> (gs : Vec Square 9) -> GameState x gs -> GameState o (move x n gs)
 oturn : (n : ℕ) -> (gs : Vec Square 9) -> GameState o gs -> GameState x (move o n gs)

--nullPlayerx : (s : Vec Square 9) -> GameState x s -> GameState o s --a player who does not move, will be remove when we tighten up the spec
--nullPlayerx bb gs = xturn 10 bb gs ---Here is where I need to go to sleeeeeeep


--sutupidPlayer : GameState -> GameState
