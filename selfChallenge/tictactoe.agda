module tictactoe where
open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
open import Data.Sum      using (_⊎_; inj₁; inj₂)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≤′_)
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

data GameCondition : Set where
 ongoing : GameCondition
 xWin : GameCondition
 oWin : GameCondition
 draw : GameCondition

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

--nullPlayerx : (s : Vec Square 9) -> GameState x s -> GameState o s --a player who does not move, will be remove when we tighten up the spec
--nullPlayerx bb gs = xturn 10 bb gs ---Here is where I need to go to sleeeeeeep


--sutupidPlayer : GameState -> GameState


-- _=== : {A : Set} -> {a : A} -> a -> Bool
-- _ ===  = false

--TODO: count :  {len :  ℕ} -> {A : Set} -> A -> Vec A len -> ℕ
count- : {len :  ℕ} -> Vec Square len -> ℕ
count- [] = 0
count- (- ∷ xs) = suc (count- xs)
count- (_ ∷ xs) = count- xs

data _==_ {A : Set}(x : A) : A -> Set where
 refl : x == x

gameCondition : {len :  ℕ} -> Vec Square len -> GameCondition
gameCondition (x ∷ x ∷ x ∷
               _ ∷ _ ∷ _ ∷
               _ ∷ _ ∷ _ ∷ [] ) = xWin

gameCondition (_ ∷ _ ∷ _ ∷
               x ∷ x ∷ x ∷
               _ ∷ _ ∷ _ ∷ [] ) = xWin

gameCondition (_ ∷ _ ∷ _ ∷
               _ ∷ _ ∷ _ ∷
               x ∷ x ∷ x ∷ [] ) = xWin

gameCondition (x ∷ _ ∷ _ ∷
               x ∷ _ ∷ _ ∷
               x ∷ _ ∷ _ ∷ [] ) = xWin

gameCondition (_ ∷ x ∷ _ ∷
               _ ∷ x ∷ _ ∷
               _ ∷ x ∷ _ ∷ [] ) = xWin

gameCondition (_ ∷ _ ∷ x ∷
               _ ∷ _ ∷ x ∷
               _ ∷ _ ∷ x ∷ [] ) = xWin

gameCondition (x ∷ _ ∷ _ ∷
               _ ∷ x ∷ _ ∷
               _ ∷ _ ∷ x ∷ [] ) = xWin

gameCondition (_ ∷ _ ∷ x ∷
               _ ∷ x ∷ _ ∷
               x ∷ _ ∷ _ ∷ [] ) = xWin

gameCondition (o ∷ o ∷ o ∷
               _ ∷ _ ∷ _ ∷
               _ ∷ _ ∷ _ ∷ [] ) = oWin

gameCondition (_ ∷ _ ∷ _ ∷
               o ∷ o ∷ o ∷
               _ ∷ _ ∷ _ ∷ [] ) = oWin

gameCondition (_ ∷ _ ∷ _ ∷
               _ ∷ _ ∷ _ ∷
               o ∷ o ∷ o ∷ [] ) = oWin

gameCondition (o ∷ _ ∷ _ ∷
               o ∷ _ ∷ _ ∷
               o ∷ _ ∷ _ ∷ [] ) = oWin

gameCondition (_ ∷ o ∷ _ ∷
               _ ∷ o ∷ _ ∷
               _ ∷ o ∷ _ ∷ [] ) = oWin

gameCondition (_ ∷ _ ∷ o ∷
               _ ∷ _ ∷ o ∷
               _ ∷ _ ∷ o ∷ [] ) = oWin

gameCondition (o ∷ _ ∷ _ ∷
               _ ∷ o ∷ _ ∷
               _ ∷ _ ∷ o ∷ [] ) = oWin

gameCondition (_ ∷ _ ∷ o ∷
               _ ∷ o ∷ _ ∷
               o ∷ _ ∷ _ ∷ [] ) = oWin
gameCondition xs with count- xs
... | 0 = draw
... | _ = ongoing

--TODO: validate with the Player
#ofMoves : {len :  ℕ} -> Vec Square len -> ℕ
#ofMoves bb with gameCondition bb
... | ongoing = count- bb
... | _ = 0

replace- : {len : ℕ} -> Square -> ℕ -> Vec Square len -> Vec Square len
replace- _ _ [] = []
replace- a 0 ( - ∷ xs ) = a ∷ xs
replace- a (suc nn) ( -  ∷ xs ) = - ∷ (replace- a nn xs)
replace- a nn ( xx  ∷ xs ) = xx ∷ (replace- a nn xs)

makeMove : {len :  ℕ} -> Vec Square len -> Player -> ℕ -> Vec Square len
makeMove bb p nn = replace- (player2Square p) nn bb

--TODO: make safe move?

--TODO: make the move validation more trancparent
data Game : Player -> Vec Square 9 -> Set where
 start : Game x ( - ∷ - ∷ - ∷
                  - ∷ - ∷ - ∷
                  - ∷ - ∷ - ∷ [] )
 xturn : {gs : Vec Square 9} -> (n : ℕ) -> Game x gs -> n < (#ofMoves gs) -> Game o (makeMove gs x n )
 oturn : {gs : Vec Square 9} -> (n : ℕ) -> Game o gs -> n < (#ofMoves gs) -> Game x (makeMove gs o n )

--I'm going to have a fun game of tictactoe, everyone loves an interface that requires a proof of move correctness with each move
g1 = start
-- allways go for the center (TODO: PROVE that you cannot force a draw another way?)
g2 = xturn 4 g1 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
-- o to the lower left corner, 
g3 = oturn 5 g2 (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
-- x to the uper right
g4 = xturn 2 g3 (s≤s (s≤s (s≤s z≤n)))
-- o to bottom middle
g5 = oturn 4 g4 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
-- x to the lower right,  THE GAME IS MINE!
g6 = xturn 4 g5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
-- o block upper left
g7 = oturn 0 g6 (s≤s z≤n)
-- x wins center right
g8 = xturn 2 g7 (s≤s (s≤s (s≤s z≤n)))
-- o trys to move again, just in case, but cannot
--g9 = oturn 0 g8 ()

--TODO: use views to make the above game a bit less hourendous?

--TODO: given nuetralworst casel game alternatives how can you make your wins ofiscated ( {tye, win in 1, win in2} is less good then {tye, win in 13, win in 20, win in 289}?


--z≤n; s≤s
--TODO: some way to view the board???
show : {pp : Player} -> {gs : Vec Square 9} -> Game pp gs -> Vec Square 9
show start = ( - ∷ - ∷ - ∷
           - ∷ - ∷ - ∷
           - ∷ - ∷ - ∷ [] )
--show xturn _ 
show _ = ( - ∷ - ∷ - ∷
           - ∷ - ∷ - ∷
           - ∷ - ∷ - ∷ [] )


showLen : {len :  ℕ} {A : Set} -> Vec A len -> ℕ
showLen ? = len

showType : {len :  ℕ} {A : Set} -> Vec A len -> Set
showType ? = A
 
data GameOver :  Vec Square 9 -> Set where
 draw : (gs : Vec Square 9) -> (count- gs) == 0 -> GameOver gs
--xWins ...



