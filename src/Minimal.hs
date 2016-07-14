{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms, PatternGuards #-}

module Minimal where

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

(#&) :: Formula -> Formula -> Formula
a #& b = Conjunction a b

(#|) :: Formula -> Formula -> Formula
a #| b = Disjunction a b

(#>) :: Formula -> Formula -> Formula
a #> b = Implication a b

pattern Bottom = Proposition "\x22A5"
pattern Not f = Implication f Bottom

instance Show Formula where
    show (Proposition s)   = s
    show (Not f)           = printf "\x00AC%s" (show f)
    show (Conjunction a b) = printf "(%s \x2227 %s)" (show a) (show b)
    show (Disjunction a b) = printf "(%s \x2228 %s)" (show a) (show b)
    show (Implication a b) = printf "(%s \x2192 %s)" (show a) (show b)

data Deduction = Deduction { assumptions :: Set Formula
                           , conclusion  :: Formula
                           } deriving (Show)

type Proof = Except String Deduction

runProof :: Proof -> Either String Deduction
runProof = runExcept

assume' :: Formula -> Deduction
assume' f = Deduction (Set.singleton f) f

implIntro' :: Formula -> Deduction -> Deduction
implIntro' f d = Deduction (Set.delete f a) (f #> c)
    where a = assumptions d
          c = conclusion d

implElim :: Deduction -> Deduction -> Proof
implElim (Deduction aA a') (Deduction aAtoB (Implication a b))
    | (a' == a) = return (Deduction (Set.union aA aAtoB) b)
    | otherwise = throwError "conclusion of first argument must be the antecedent of the conclusion of the second argument"
implElim _ _ = throwError "second argument to implElim must be an implication"

conjIntro' :: Deduction -> Deduction -> Deduction
conjIntro' l r = Deduction (Set.union al ar) (cl #& cr)
    where al = assumptions l
          ar = assumptions r
          cl = conclusion l
          cr = conclusion r

leftDisjIntro' :: Formula -> Deduction -> Deduction
leftDisjIntro' f d = Deduction (assumptions d) (f #| r)
    where r = conclusion d

rightDisjIntro' :: Deduction -> Formula -> Deduction
rightDisjIntro' d f = Deduction (assumptions d) (l #| f)
    where l = conclusion d

leftConjElim :: Deduction -> Proof
leftConjElim d = case (conclusion d) of
    (Conjunction _ r) -> return d { conclusion = r }
    _                 -> throwError "argument must be a conjunction"

rightConjElim :: Deduction -> Proof
rightConjElim d = case (conclusion d) of
    (Conjunction l _) -> return d { conclusion = l }
    _                 -> throwError "argument must be a conjunction"

disjElim :: Deduction -> Deduction -> Deduction -> Proof
disjElim avb atoc btoc
    | conclusion atoc == conclusion btoc = disjElimSame
    | otherwise = throwError "conclusion of second arg and conclusion of third arg must be equal"
    where disjElimSame = case (conclusion avb) of
              (Disjunction a b) -> return (Deduction (Set.unions [g, hA, hB]) c)
                where g = assumptions avb
                      hA = assumptions atoc \\ Set.singleton a
                      hB = assumptions btoc \\ Set.singleton b
                      c = conclusion atoc
              _ -> throwError "conclusion of first arg must be a disjunction"

-- These allow for a more consistent syntax when doing proofs
assume :: Formula -> Proof
assume f = return $ assume' f

conjIntro :: Deduction -> Deduction -> Proof
conjIntro l r = return $ conjIntro' l r

implIntro :: Formula -> Deduction -> Proof
implIntro f d = return $ implIntro' f d

leftDisjIntro :: Formula -> Deduction -> Proof
leftDisjIntro f d = return $ leftDisjIntro' f d

rightDisjIntro :: Deduction -> Formula -> Proof
rightDisjIntro d f = return $ rightDisjIntro' d f

exampleVacuousIntro = do
    let p = Proposition "P"
    let q = Proposition "Q"
    dQ <- assume q
    implIntro p dQ

exampleTransitive a dAtoB dBtoC = do
    dA <- assume a
    dB <- implElim dA dAtoB
    dC <- implElim dB dBtoC
    implIntro a dC

pp :: Formula -> Formula -> Formula
pp a b = ((a #> b) #> a) #> a

examplePPimplWT = do
    let phi = Proposition "phi"
    let psi = Proposition "psi"
    let notPhiToPsi = (Not (phi #> psi))
    dNotPhi         <- assume (Not phi)
    dBotToPsi       <- assume (Bottom #> psi)
    dPhiToPsi       <- exampleTransitive phi dNotPhi dBotToPsi
    dNotPhiToPsi    <- assume notPhiToPsi
    dBot            <- implElim dPhiToPsi dNotPhiToPsi
    dBotToPsiToBot  <- implIntro (Bottom #> psi) dBot
    dPP             <- assume (pp Bottom psi)
    dBot'           <- implElim dBotToPsiToBot dPP
    dNotNotPhiToPsi <- implIntro notPhiToPsi dBot'
    implIntro (Not phi) dNotNotPhiToPsi

