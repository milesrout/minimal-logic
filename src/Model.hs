{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms, PatternGuards #-}

module Model where

import Minimal
import Data.List
import Text.Printf
import Data.Set (Set, (\\))
import qualified Data.Set as Set

-- A type alias to make the code clearer
type PropositionalSymbol = String

-- Kripke "possible world" semantics (see http://arxiv.org/pdf/1606.08092v1.pdf)
data Model = Model
    { abnormalWorlds :: Set World
    , rootWorld      :: World
    } deriving (Eq, Ord, Show)

data World = World
    { forcedProps :: Set PropositionalSymbol
    , childWorlds :: Set World
    , name        :: String
    } deriving (Eq, Ord)

instance Show World where
    show (World _ _ name) = name

-- Haskell has Set.unions :: [Set a] -> Set a
-- and Set.union :: Set a -> Set a -> Set a
-- but not this:
setFlatten :: (Ord a) => Set (Set a) -> Set a
setFlatten = Set.unions . Set.toList

cone :: World -> Set World
cone w = ((Set.insert w) . setFlatten . (Set.map cone) . childWorlds) w


checkModel :: Formula -> Model -> Bool
checkModel f m = and [checkWorld f w | w <- (Set.toList . cone . rootWorld) m]
    where checkWorld :: Formula -> World -> Bool
          checkWorld Bottom            w = w `Set.member` abnormalWorlds m
          checkWorld (Proposition p)   w = p `Set.member` forcedProps w
          checkWorld (Conjunction a b) w = checkWorld a w && checkWorld b w
          checkWorld (Disjunction a b) w = checkWorld a w || checkWorld b w
          checkWorld (Implication a b) w = and [checkImpl a b v | v <- Set.toList (cone w)]

          checkImpl :: Formula -> Formula -> World -> Bool
          checkImpl a b w = not (checkWorld a w) || checkWorld b w
