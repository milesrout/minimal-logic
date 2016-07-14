{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns, PatternSynonyms, PatternGuards #-}

module Minimal where

import Text.Printf (printf)
import Data.Set (Set, (\\))
import qualified Data.Set as Set

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

{-
 - NAME         NUM ASSUMPS     STACK
 - Assume       +1              { - a }
 - ConjIntro    0               { a b - a^b }
 - LDisjIntro   0               { a - a^b }
 - RDisjIntro   0               { b - a^b }
 - LConjElim    0               { a^b - b }
 - RConjElim    0               { a^b - a }
 - DisjElim     2               { avb a>c b>c - c }
 -
 - Assume     : takes F and gives a proof of F from {F}
 - ConjIntro  : takes a proof of A from G and a proof of B from H and
 -              gives a proof of A^B from G U H
 - LDisjIntro : takes a proof of B from G and gives a proof of AvB from G
 - LDisjIntro : takes a A and proof of B from G 
 -              and gives a proof of AvB from G
 - RDisjIntro : takes a proof of A from G and B
 -              and gives a proof of AvB from G
 - LConjElim  : takes a proof of A^B from G and gives a proof of B from G
 - RConjElim  : takes a proof of A^B from G and gives a proof of A from G
 - DisjElim   : takes a proof of AvB from G, a proof of C from H1 U {A}
 -              and a proof of C from H2 U {B}, and gives a proof of 
 -              C from G U H1 U H2.
 - ImplElim   : takes a proof of A>B from G and a proof of A from H
 -              and gives a proof of B from G U H
 - ImplIntro  : takes a proof of B from G U {A} and gives a proof of
 -              A>B from G
 -}

data Deduction = Deduction { assumptions :: Set Formula,
                             conclusion  :: Formula
                           } deriving (Show)

assume' :: Formula -> Deduction
assume' f = Deduction (Set.singleton f) f

implIntro' :: Formula -> Deduction -> Deduction
implIntro' f d = Deduction (Set.delete f a) (f #> c)
    where a = assumptions d
          c = conclusion d

implElim :: Deduction -> Deduction -> Maybe Deduction
implElim (Deduction aA a') (Deduction aAtoB (Implication a b))
    | (a' == a) = Just $ (Deduction (Set.union aA aAtoB) b)
    | otherwise = Nothing
implElim _ _ = Nothing

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

leftConjElim :: Deduction -> Maybe Deduction
leftConjElim d = case (conclusion d) of
    (Conjunction _ r) -> Just d { conclusion = r }
    _                 -> Nothing

rightConjElim :: Deduction -> Maybe Deduction
rightConjElim d = case (conclusion d) of
    (Conjunction l _) -> Just d { conclusion = l }
    _                 -> Nothing

disjElim :: Deduction -> Deduction -> Deduction -> Maybe Deduction
disjElim avb atoc btoc
    | conclusion atoc == conclusion btoc = disjElimSame
    | otherwise                          = Nothing
    where disjElimSame = case (conclusion avb) of
              (Disjunction a b) -> Just (Deduction (Set.unions [g, hA, hB]) c)
                where g = assumptions avb
                      hA = assumptions atoc \\ Set.singleton a
                      hB = assumptions btoc \\ Set.singleton b
                      c = conclusion atoc
              _                 -> Nothing

-- These allow for a more consistent syntax when doing proofs
assume :: Formula -> Maybe Deduction
assume f = Just $ assume' f

conjIntro :: Deduction -> Deduction -> Maybe Deduction
conjIntro l r = Just $ conjIntro' l r

implIntro :: Formula -> Deduction -> Maybe Deduction
implIntro f d = Just $ implIntro' f d

leftDisjIntro :: Formula -> Deduction -> Maybe Deduction
leftDisjIntro f d = Just $ leftDisjIntro' f d

rightDisjIntro :: Deduction -> Formula -> Maybe Deduction
rightDisjIntro d f = Just $ rightDisjIntro' d f

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

