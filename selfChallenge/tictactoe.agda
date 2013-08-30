module tictactoe where
open import Data.Empty    using (⊥)
open import Data.Unit     using (⊤; tt)
--open import Data.Sum      using (_⊎_; inj₁; inj₂)
--open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _≤′_; _≤?_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe
open import Data.Fin using (Fin; fromℕ≤; toℕ; #_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Binary


data Player : Set where
 x o : Player

data Square : Set where
 - x o : Square

data GameCondition : Set where
 ongoing : GameCondition
 xWin : GameCondition
 oWin : GameCondition
 draw : GameCondition

--TODO: are structures like this more or less readable?
{- ...
data Square' : Set where
 - : Square'
 taken : Player -> Square'

data GameOver' : Set where
 Win : Player -> GameOver'
 draw : GameOver'

data GameCondition' : Set where
 ongoing : GameCondition'
 done :  GameOver' -> GameCondition'
...-}

--TODO: alias Vec Square 9 to Bourd for easy reading

-- A nice language would let you make this an implicit converion
player2Square : Player -> Square
player2Square x = x
player2Square o = o 


--TODO: count :  {len :  ℕ} -> {A : Set} -> A -> Vec A len -> ℕ
count- : {len :  ℕ} -> Vec Square len -> ℕ
count- [] = 0
count- (- ∷ xs) = suc (count- xs)
count- (_ ∷ xs) = count- xs


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

-- TODO: make replace safe with finite and such
replace- : {len : ℕ} -> Square -> ℕ -> Vec Square len -> Vec Square len
replace- _ _ [] = []
replace- a 0 ( - ∷ xs ) = a ∷ xs
replace- a (suc nn) ( -  ∷ xs ) = - ∷ (replace- a nn xs)
replace- a nn ( xx  ∷ xs ) = xx ∷ (replace- a nn xs)

makeMove : {len :  ℕ} -> (gs : Vec Square len) -> Player -> Fin (#ofMoves gs) -> Vec Square len
makeMove bb p nn = replace- (player2Square p) (toℕ nn) bb


--TODO: make the move validation more trancparent
data Game : Player -> Vec Square 9 -> Set where
 start : Game x ( - ∷ - ∷ - ∷
                  - ∷ - ∷ - ∷
                  - ∷ - ∷ - ∷ [] )
 xturn : {gs : Vec Square 9} -> (m : Fin (#ofMoves gs)) -> Game x gs -> Game o (makeMove gs x m )
 oturn : {gs : Vec Square 9} -> (m : Fin (#ofMoves gs)) -> Game o gs -> Game x (makeMove gs o m )

--I'm going to have a fun game of tictactoe, everyone loves an interface that requires a proof of move correctness with each move
g1 = start
-- allways go for the center (TODO: PROVE that you cannot force a draw another way?)
g2 = xturn (# 4)  g1
-- o to the lower left corner, 
g3 = oturn (# 5) g2
-- x to the uper right
g4 = xturn (# 2) g3
-- o to bottom middle
g5 = oturn (# 4) g4
-- x to the lower right,  THE GAME IS MINE!
g6 = xturn (# 4) g5
-- o block upper left
g7 = oturn (# 0) g6
-- x wins center right
g8 = xturn (# 2) g7
-- o trys to move again, just in case, but cannot
--g9 = oturn (# 0) g8

_≤′'_ : ℕ → ℕ → Set
zero  ≤′' n     = ⊤
suc m ≤′' zero  = ⊥
suc m ≤′' suc n = m ≤′' n

f′ : {n m : ℕ} → n ≤′' m → n ≤′' suc m
f′ {zero} {m} tt = tt
f′ {suc n} {zero} ()
f′ {suc n} {suc m} xxx = f′ {n} {m} xxx

is2 : ℕ → Set
is2 2 = ⊤
is2 _ = ⊥

isEven : ℕ → Set
isEven 0 = ⊤
isEven 1 = ⊥
isEven (suc (suc xxx)) = isEven xxx 

--("a" stands for awesome)
aprop : {n : ℕ} → is2 n → isEven n
aprop {2} tt = tt
aprop {0} ()
aprop {1} ()
aprop {suc (suc (suc xxx))} ()

wha : (nn :  ℕ)  -> nn ≡ 1 -> Fin nn
wha 1 _ = # 0
wha 0 ()
wha (suc (suc _)) ()

whaa : (nn :  ℕ)  -> nn ≡ 2 -> Fin nn
whaa 2 _ = # 1
whaa 1 ()
whaa 0 ()
whaa (suc (suc (suc _))) ()

whaaaa : 1 ≡ 0  → ⊥
whaaaa ()

whaaaaa : 1 ≢ 0
whaaaaa ()

whaaaaaa : (nn :  ℕ) -> (suc nn) ≢ 0
whaaaaaa _ ()

z≡z : 0 ≡ 0
z≡z = refl 

¬¬z≡z : ((0 ≡ 0 → ⊥) → ⊥)
¬¬z≡z hh = hh refl

bleh :  (nn :  ℕ)  -> (nn ≡ 0 → ⊥) -> ℕ
bleh 0 hh with hh refl
... | ()
bleh (suc nn) _ = nn

safe : (nn :  ℕ)  -> nn ≢ 0 -> Fin nn
safe 0  hh with hh refl
... | ()
safe (suc _) _ = # 0

better : (nn :  ℕ)  -> Fin (suc nn)
better _ = # 0

--tiny : (nn :  ℕ)  -> nn ≢ 0 -> Fin nn
--tiny 0 ?
--tiny _ _ = # 0 
--"It's just cold out"

--this is an excersice in maddness just use this instead
hu : (nn :  ℕ)  -> Fin (suc nn)
hu _ = # 0

crazy : ℕ -> ℕ
crazy 0 = 10
crazy 1 = 0
crazy 2 = 0
crazy 3 = 1
crazy 4 = 0
crazy xxx = xxx

cSafe : (mm : ℕ)  -> (nn :  ℕ) -> nn ≡ (crazy mm) -> nn ≢ 0 -> Fin nn
cSafe _ 0 _  hh with hh refl
... | ()
cSafe _ (suc _) _ _ = # 0


#ofThings : {len :  ℕ} -> Vec Square len -> ℕ
#ofThings bb = count- bb

smaller : {len :  ℕ} -> {nn :  ℕ} -> (vs : Vec Square len) -> nn ≡ (#ofThings (vs)) -> nn ≢ 0 -> Fin nn
smaller {_} {0} _ _ hh with hh refl
... | ()
smaller {_} {suc _} _ _ _ = # 0 


--TODO: reason against the "with" construct



--As a gentlemens game there is no need for verifiactaion of move validity (yeah right)
--TODO: paramiterize this by player, There only needs to be 1 stupid!
--stupidPlayerX : {gs : Vec Square 9} -> {newgs : Vec Square 9} -> (1 ≤ (#ofMoves gs) ) -> Game x gs  -> Game o newgs
--stupidPlayer : {gs : Vec Square 9} -> (0 ≢ (#ofMoves gs)) -> (pp : Player) -> Game pp gs -> Fin (#ofMoves gs)
--stupidPlayer {_} _ _ _ = # 0



--stupidPlayerO : {gs : Vec Square 9} -> Game o gs -> (0 < (#ofMoves gs)) -> Game x (makeMove gs o _ )
--stupidPlayerO {gs} game correct  = oturn 0 game correct

{-
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


data _==_ {A : Set}(x : A) : A -> Set where
 refl : x == x




--TODO: use views to make the above game a bit less hourendous?

--TODO: given nuetralworst casel game alternatives how can you make your wins ofiscated ( {tye, win in 1, win in2} is less good then {tye, win in 13, win in 20, win in 289}?


--z≤n; s≤s
-- some way to view the board!!!
show : {pp : Player} -> {gs : Vec Square 9} -> Game pp gs -> Vec Square 9
show {_} {gs} _ = gs

getPlayer : {pp : Player} -> {gs : Vec Square 9} -> Game pp gs -> Player
getPlayer {pp} {_} _ = pp


--two programs enter, one program leaves
gameMaster : {p : Player } -> {gs : Vec Square 9} --FOR ALL
 -> ({gs : Vec Square 9} -> Game x gs -> (0 < (#ofMoves gs)) -> Game o (makeMove gs x _ )) --take an x player
 -> ({gs : Vec Square 9} -> Game o gs -> (0 < (#ofMoves gs)) -> Game x (makeMove gs o _ )) --take an o player
 -> ( Game p gs)  --Take an initial configuration
 -> GameCondition --retun a winner --TODO: how do I exclude ongoing?  Should it be excluded structualy?
gameMaster {_} {gs} _ _ game with (gameCondition gs)
... | xWin = xWin
... | oWin = oWin
... | draw = draw
... | ongoing  with #ofMoves gs | inspect #ofMoves gs
gameMaster _ _ _ | ongoing | 0 | _  = draw --TODO: really just prove this state doesn't exist, it will always be covered by gameCondition gs = draw
gameMaster {x} {gs} fx fo game | ongoing | suc nn | _ = gameMaster (fx) (fo) (fx game (s≤s z≤n)) -- x move
gameMaster {o} {gs} fx fo game | ongoing | suc nn | _ = gameMaster (fx) (fo) (fo game (s≤s z≤n)) -- o move

--TODO: find out what all this fucking yellow highlighting means

 
data GameOver :  Vec Square 9 -> Set where
 draw : (gs : Vec Square 9) -> (count- gs) == 0 -> GameOver gs
--xWins ...

-}

