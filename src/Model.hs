{-# LANGUAGE GADTs #-}

module Model where

import Minimal
import Control.Monad
import Data.List
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Text.Printf

-- Kripke "possible world" semantics for minimal logic
-- (see http://arxiv.org/pdf/1606.08092v1.pdf)
-- name is required to be unique
data Model = Model
    { root :: World
    , abnWorlds :: [World]
    } deriving (Eq, Ord)

data World = World
    { children :: [World]
    , name     :: Char
    } deriving (Eq, Ord)

instance Show Model where
    show (Model r a) = printf "{%s %s}" (show r) (show a)

instance Show World where
    show (World [] name) = [name]
    show (World ws name) = printf "(%s %s)" [name] childNames
            where childNames = intercalate " " (map show ws)

--- Get the upwards closure of a single world.
cone :: World -> [World]
cone w = insert w (join (map cone (children w)))

--- A model formed by taking Q to be all worlds.
loBOTomy :: Model -> Model
loBOTomy m = m { abnWorlds = cone (root m) }

--- Check whether a formula is forced by a model.
checkModel :: Model -> AnyFormula -> Bool
checkModel m f = checkWorldRecur (root m) f
    where checkWorldRecur :: World -> AnyFormula -> Bool
          checkWorldRecur w f = and [checkWorld w f | w <- cone w]

          checkWorld :: World -> AnyFormula -> Bool
          checkWorld w (MkAF Bot)        = w `elem` (abnWorlds m)
          checkWorld w (MkAF (Prop p))   = name w `elem` p
          checkWorld w (MkAF (Conj a b)) = checkWorld w (MkAF a) && checkWorld w (MkAF b)
          checkWorld w (MkAF (Disj a b)) = checkWorld w (MkAF a) || checkWorld w (MkAF b)
          checkWorld w (MkAF (Impl a b)) = and [checkImpl (MkAF a) (MkAF b) v | v <- cone w]

          checkImpl :: AnyFormula -> AnyFormula -> World -> Bool
          checkImpl a b w = not (checkWorldRecur w a) || checkWorldRecur w b

wK :: World
wK = World [] 'K'

m1 = Model wK []
m1l = loBOTomy m1

wM, wN :: World
wM = World [] 'M'
wN = World [wM] 'N'

m2 = Model wN []
m2' = Model wN [wM]
m2l = loBOTomy m2

wW, wU, wV :: World
wW = World [] 'W'
wU = World [] 'U'
wV = World [wW,wU] 'V'

m3 = Model wV []
m3' = Model wV [wW, wU]
m3l = loBOTomy m3

wA, wB, wC, wD :: World
wA = World [] 'A'
wB = World [wA] 'B'
wC = World [wA] 'C'
wD = World [wB,wC] 'D'

m4 = Model wD []
m4l = loBOTomy m4

wF, wG, wH, wI :: World
wF = World [] 'F'
wG = World [] 'G'
wH = World [wG] 'H'
wI = World [wF,wH] 'I'

m5 = Model wI [wG]

--- This allows us to make the following code polymorphic over the number of
--- schematic variables.
data Schema = Schema1 (AnyFormula -> AnyFormula)
            | Schema2 (AnyFormula -> AnyFormula -> AnyFormula)
            | Schema3 (AnyFormula -> AnyFormula -> AnyFormula -> AnyFormula)

--- Return one proposition for every upwards closed subset of the worlds in a model.
truthValues :: Model -> [AnyFormula]
truthValues m = [afBot] ++ (map upSetToProposition (upsets m))

--- Come up with a name for a given upwards closed set
upSetToProposition :: [World] -> AnyFormula
upSetToProposition [] = afProp "\x2205" -- $\emptyset$
upSetToProposition ws = afProp (map name ws)

--- Return all upwards closed sets of worlds in a model.
upsets :: Model -> [[World]]
upsets m = sortUniq (map closure (allWorldsSubsets m))

--- Sort then remove duplicates
sortUniq :: (Ord a) => [a] -> [a]
sortUniq xs = nub (sort xs)

--- All subsets of worlds of a model
allWorldsSubsets :: Model -> [[World]]
allWorldsSubsets m = subsequences (cone (root m))

--- Closure w.r.t. the forcing relation
closure :: [World] -> [World]
closure ws = sortUniq (join (map cone ws))

--- Check whether for every assignment of truth values from the model to
--- schematic variables in the given axiom schema, the schema holds.
checkSchema :: Schema -> Model -> Bool
checkSchema s m = and (map (checkModel m) (appls s m))

--- Find an assignment of propositions to the scheme that fails in the model.
findCounterexample :: Schema -> Model -> [AnyFormula]
findCounterexample s m = filter (\f -> not (checkModel m f)) (appls s m)

--- Generate all the assignments of propositions in the scheme that fail in the model.
appls :: Schema -> Model -> [AnyFormula]
appls (Schema1 s) m = do
    p <- truthValues m
    return (s p)
appls (Schema2 s) m = do
    p <- truthValues m
    q <- truthValues m
    return (s p q)
appls (Schema3 s) m = do
    p <- truthValues m
    q <- truthValues m
    r <- truthValues m
    return (s p q r)

printInstances :: Schema -> Model -> IO ()
printInstances s m = forM_ (appls s m) (\f -> do
    putStrLn (printf "%s: %s" (show f) (show (checkModel m f))))

--(!&) :: AnyFormula -> AnyFormula -> AnyFormula
--(!|) :: AnyFormula -> AnyFormula -> AnyFormula
--(!>) :: AnyFormula -> AnyFormula -> AnyFormula

afBot :: AnyFormula
afBot = MkAF Bot

afNot :: AnyFormula -> AnyFormula
afNot f = f !> afBot

afProp s = MkAF (Prop s)

a !& b = case a of
    (MkAF xA) -> case b of
        (MkAF xB) -> MkAF $ xA #& xB
a !| b = case a of
    (MkAF xA) -> case b of
        (MkAF xB) -> MkAF $ xA #| xB
a !> b = case a of
    (MkAF xA) -> case b of
        (MkAF xB) -> MkAF $ xA #> xB

sDNE  = Schema1 (\a -> (afNot (afNot a)) !> a)
sDGP  = Schema2 (\a b -> (a !> b) !| (b !> a))
sEFQ  = Schema1 (\a -> afBot !> a)
sLEM  = Schema1 (\a -> a !| afNot a)
sPP   = Schema2 (\a b-> ((a !> b) !> a) !> a)
sWLEM = Schema1 (\a -> afNot a !| afNot (afNot a))
sDGPA = Schema2 (\a b -> afNot (a !> b) !> afNot (afNot (b !> a)))
sTFA  = Schema2 (\a b -> afNot a !> afNot (afNot (a !> b)))

schemata :: [Schema]
schemata = [sDNE, sEFQ, sLEM, sDGP, sPP, sWLEM, sTFA, sDGPA]

models :: [Model]
models = [m1, m1l, m2, m2l, m2', m3, m3l, m3', m4, m4l]

printResults :: IO ()
printResults = forM_ (transpose [map (checkSchema s) models | s <- schemata]) (putStrLn.show)

-- [True,True,True,True,True,True,True,True]
-- [False,False,True,True,True,True,True,True]
-- [False,True,False,True,False,True,True,True]
-- [False,False,True,True,False,True,True,True]
-- [False,False,True,True,False,True,False,True]
-- [False,True,False,False,False,False,True,True]
-- [False,False,True,False,False,True,True,True]
-- [False,False,True,False,False,True,False,False]
-- [False,True,False,False,False,True,True,True]
-- [False,False,True,False,False,True,True,True]
