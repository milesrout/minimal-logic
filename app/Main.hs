module Main where

import Control.Monad
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)

import Minimal
import Model

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

phi, psi, notPhiToPsi :: Formula
phi = Proposition "phi"
psi = Proposition "psi"
notPhiToPsi = Not (phi #> psi)

examplePPimplWT = do
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


fP, fQ :: Formula
fP = Proposition "P"
fQ = Proposition "Q"

pP, pQ, pR, pS :: PropositionalSymbol
pP = "P"
pQ = "Q"
pR = "R"
pS = "S"

exM1_W1 = World (Set.singleton "P") Set.empty "w1"
exM1 = Model Set.empty exM2_W1

exM2_W2 = World (Set.fromList ["P","Q"]) Set.empty                "w2"
exM2_W1 = World (Set.fromList ["P"])     (Set.fromList [exM2_W2]) "w1"
exM2 = Model (Set.singleton exM2_W2) exM2_W1

exM3_W4 = World (Set.fromList ["P"]) Set.empty                        "w4"
exM3_W3 = World (Set.fromList [])    (Set.fromList [exM3_W4])         "w3"
exM3_W2 = World (Set.fromList ["P"]) Set.empty                        "w2"
exM3_W1 = World (Set.fromList [])    (Set.fromList [exM3_W2,exM3_W3]) "w1"
exM3 = Model (Set.singleton exM3_W4) exM3_W1

lem p = p #| Not p
examples = [pp a b | a <- [fP,Bottom], b <- [fP,Bottom]]

wlemN :: Integer -> Formula
wlemN n = antecedent #> consequent
    where antecedent = Not $ foldl1' Disjunction (propPairs n)
          consequent = foldl1' Disjunction (notProps n)

lemN :: Integer -> Formula
lemN n = antecedent #> consequent
    where antecedent = Not $ foldl1' Disjunction (notPropPairs n)
          consequent = foldl1' Disjunction (props n)

prop :: Integer -> Formula
prop i = Proposition ("P" ++ show i)

propPairs, notPropPairs :: Integer -> [Formula]
propPairs    = conjPairs prop
notPropPairs = conjPairs (Not . prop)

props, notProps :: Integer -> [Formula]
props    n = map prop [1..n]
notProps n = map (Not . prop) [1..n]

conjPairs :: (Integer -> Formula) -> Integer -> [Formula]
conjPairs p n = [p i #& p j | (i,j) <- pairs n]

pairs :: Integer -> [(Integer, Integer)]
pairs n = [(i,j) | i <- [1..n], j <- [1..n], i < j]

compose :: Deduction -> Deduction -> Proof
compose dAB dBC = do
    -- get the antecedent of the conclusion of dAB
    let (Implication a _) = conclusion dAB
    dA  <- assume a
    dB  <- implElim dA dAB
    dC  <- implElim dB dBC
    dAC <- implIntro a dC
    return dAC

pAB, pBC, pAC :: Proof
pAB = assume (Proposition "A" #> Proposition "B")
pBC = assume (Proposition "B" #> Proposition "C")
pAC = do
    dAB <- pAB
    dBC <- pBC
    compose dAB dBC


main :: IO ()
main = putStrLn "Hello, world!"
