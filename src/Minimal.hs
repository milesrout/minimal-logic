{-# LANGUAGE ViewPatterns, PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}

module Minimal where
--module Minimal (
--    Formula(..),
--    (#&), (#|), (#>),
--    bot,
--    pattern Bottom,
--    pattern Not,
--    Deduction(..),
--    Proof(..),
--    runProof, evalProof, throwError,
--    assume,
--    implIntro, implElim,
--    conjIntro, leftConjElim, rightConjElim,
--    disjElim, leftDisjIntro, rightDisjIntro,
--    ) where

import Control.Monad.Except
import Control.Monad.Free
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Text.Printf (printf)

data Formula
    = Proposition String
    | Conjunction Formula Formula
    | Disjunction Formula Formula
    | Implication Formula Formula
    deriving (Eq, Ord)

-- These are just shorthand
(#&) :: Formula -> Formula -> Formula
a #& b = Conjunction a b

(#|) :: Formula -> Formula -> Formula
a #| b = Disjunction a b

(#>) :: Formula -> Formula -> Formula
a #> b = Implication a b

-- These 'pattern synonyms' allow pattern-matching on Bottom and (Not f). 
bot = "\x22A5"
pattern Bottom = Proposition "\x22A5"
pattern Not f = Implication f Bottom

-- The Unicode literals are the Unicode equivalents of LaTeX's \neg (\lnot),
-- \wedge (\land), \vee (\lor) and \to respectively.
-- This specifies how a Formula should be converted into a string.
instance Show Formula where
    show (Proposition s)   = s
    show (Not f)           = printf "\x00AC%s" (show f)
    show (Conjunction a b) = printf "(%s \x2227 %s)" (show a) (show b)
    show (Disjunction a b) = printf "(%s \x2228 %s)" (show a) (show b)
    show (Implication a b) = printf "(%s \x2192 %s)" (show a) (show b)

data Proof = Proof { assumptions :: Set Formula
                   , conclusion  :: Formula
                   } deriving (Show)

data DeductionF next
    = Assume Formula (Proof -> next)
    | ImplElim Proof Proof (Proof -> next)
    | ImplIntro Formula Proof (Proof -> next)
    deriving (Functor)

type Deduction = Free DeductionF

assume :: Formula -> Deduction Proof
assume f = liftF (Assume f id)

implElim :: Proof -> Proof -> Deduction Proof
implElim maj min = liftF (ImplElim maj min id)

implIntro :: Formula -> Proof -> Deduction Proof
implIntro f prem = liftF (ImplIntro f prem id)

blah :: Deduction Proof
blah = do
    dA  <- assume (Proposition "A")
    dNA <- assume (Not (Proposition "A"))
    dB  <- implElim dNA dA
    implIntro (Not (Proposition "A")) dB

showDeduction :: (Show a, Show r) => Free (DeductionF a) r -> String
showDeduction (Free (Assume f x)) = printf "assume %s\n %s" 
