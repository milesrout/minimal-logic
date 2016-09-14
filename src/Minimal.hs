{-# LANGUAGE ViewPatterns, PatternSynonyms #-}

module Minimal (
    Formula(..),
    (#&), (#|), (#>),
    bot,
    pattern Bottom,
    pattern Not,
    Deduction(..),
    Proof(..),
    runProof, evalProof, throwError,
    assume,
    implIntro, implElim,
    conjIntro, leftConjElim, rightConjElim,
    disjElim, leftDisjIntro, rightDisjIntro,
    ) where

import Control.Monad.Except
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

data Deduction = Deduction { assumptions :: Set Formula
                           , conclusion  :: Formula
                           } deriving (Show)

-- Except is like Either (sum type) but explicitly for representing errors.
type Proof = Except String Deduction

runProof :: Proof -> Either String Deduction
runProof = runExcept

evalProof :: Proof -> Deduction
evalProof p = case runProof p of
    (Right d) -> d
    _         -> error "evalProof run on invalid Proof"

-- The quoted versions of these functions are ones that can't fail, so return
-- Deduction instead of Proof. Unquoted versions are defined below that return
-- a Proof for consistency.

assume :: Formula -> Proof
assume f = return (Deduction (Set.singleton f) f)

implIntro :: Formula -> Deduction -> Proof
implIntro f d = return (Deduction (Set.delete f a) (f #> c))
    where a = assumptions d
          c = conclusion d

implElim :: Deduction -> Deduction -> Proof
implElim (Deduction aA a') (Deduction aAtoB (Implication a b))
    | (a' == a) = return (Deduction (Set.union aA aAtoB) b)
    | otherwise = throwError "conclusion of first argument must be the antecedent of the conclusion of the second argument"
implElim _ _ = throwError "second argument to implElim must be an implication"

conjIntro :: Deduction -> Deduction -> Proof
conjIntro l r = return (Deduction (Set.union al ar) (cl #& cr))
    where al = assumptions l
          ar = assumptions r
          cl = conclusion l
          cr = conclusion r

leftDisjIntro :: Formula -> Deduction -> Proof
leftDisjIntro f d = return (Deduction (assumptions d) (f #| r))
    where r = conclusion d

rightDisjIntro :: Deduction -> Formula -> Proof
rightDisjIntro d f = return (Deduction (assumptions d) (l #| f))
    where l = conclusion d

leftConjElim :: Deduction -> Proof
leftConjElim d = case (conclusion d) of
    (Conjunction _ r) -> return d { conclusion = r }
    _ -> throwError "argument must be a conjunction"

rightConjElim :: Deduction -> Proof
rightConjElim d = case (conclusion d) of
    (Conjunction l _) -> return d { conclusion = l }
    _ -> throwError "argument must be a conjunction"

disjElim :: Deduction -> Deduction -> Deduction -> Proof
-- matches if the conclusion of the first argument is a disjunction.
-- then binds the whole deduction to `aOrB'.
disjElim aOrB@(conclusion -> (Disjunction a b)) aToC bToC
    | conclusion aToC == conclusion bToC = return (Deduction assums conc)
    | otherwise = throwError "conclusion of second arg and conclusion of third arg must be equal"
        where aAorB = assumptions aOrB
              aAtoC = a `Set.delete` assumptions aToC
              aBtoC = b `Set.delete` assumptions bToC
              assums = Set.unions [aAorB, aAtoC, aBtoC]
              conc = conclusion aToC
disjElim _ _ _ = throwError "conclusion of first arg must be a disjunction"
