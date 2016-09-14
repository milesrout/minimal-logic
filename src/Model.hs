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
checkModel :: Model -> Formula -> Bool
checkModel m f = checkWorldRecur (root m) f
    where checkWorldRecur :: World -> Formula -> Bool
          checkWorldRecur w f = and [checkWorld w f | w <- cone w]

          checkWorld :: World -> Formula -> Bool
          checkWorld w Bottom            = w `elem` (abnWorlds m)
          checkWorld w (Proposition p)   = name w `elem` p
          checkWorld w (Conjunction a b) = checkWorld w a && checkWorld w b
          checkWorld w (Disjunction a b) = checkWorld w a || checkWorld w b
          checkWorld w (Implication a b) = and [checkImpl a b v | v <- cone w]

          checkImpl :: Formula -> Formula -> World -> Bool
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
data Schema = Schema1 (Formula -> Formula)
            | Schema2 (Formula -> Formula -> Formula)
            | Schema3 (Formula -> Formula -> Formula -> Formula)

--- Return one proposition for every upwards closed subset of the worlds in a model.
truthValues :: Model -> [Formula]
truthValues m = [Bottom] ++ (map upSetToProposition (upsets m))

--- Come up with a name for a given upwards closed set
upSetToProposition :: [World] -> Formula
upSetToProposition [] = Proposition "\x2205" -- $\emptyset$
upSetToProposition ws = Proposition (map name ws)

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
findCounterexample :: Schema -> Model -> [Formula]
findCounterexample s m = filter (\f -> not (checkModel m f)) (appls s m)

--- Generate all the assignments of propositions in the scheme that fail in the model.
appls :: Schema -> Model -> [Formula]
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

sDNE  = Schema1 (\a -> (Not (Not a)) #> a)
sDGP  = Schema2 (\a b -> (a #> b) #| (b #> a))
sEFQ  = Schema1 (\a -> Bottom #> a)
sLEM  = Schema1 (\a -> a #| Not a)
sPP   = Schema2 (\a b-> ((a #> b) #> a) #> a)
sWLEM = Schema1 (\a -> Not a #| Not (Not a))
sDGPA = Schema2 (\a b -> Not (a #> b) #> Not (Not (b #> a)))
sTFA  = Schema2 (\a b -> Not a #> Not (Not (a #> b)))

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
