module Equivalences where

import Control.Monad
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)

import Minimal
import Model

--doubleNegElim :: Deduction -> Proof
--doubleNegElim dNNP = case conclusion dNNP of
--    (Not (Not f)) -> return $ Deduction assumps f
--        where assumps = aDNE `Set.insert` assumptions dNNP
--              aDNE = Not (Not f) #> f
--    _ -> throwError "DNE must only be applied to double negations"
--
--phi :: Formula
--phi = Proposition "phi"
--
--dneImplAristotle :: Deduction
--dneImplAristotle = evalProof $ do
--    d1 <- assume (Not phi)
--    d2 <- implIntro phi d1
--    d3 <- assume (Not (phi #> Not phi))
--    d4 <- implElim d2 d3
--    d5 <- implIntro (Not phi) d4
--    d6 <- doubleNegElim d5
--    d7 <- implIntro (Not (phi #> Not phi)) d6
--    return d7
--
--aristotleImplDne :: Deduction
--aristotleImplDne = evalProof $ do
--    d1  <- assume phi
--    d2  <- assume (phi #> Not phi)
--    d3  <- implElim d1 d2
--    d4  <- assume (Not (Not phi))
--    d5  <- implElim d3 d4
--    d6  <- implIntro phi d5
--    d7  <- implElim d6 d4
--    d8  <- implIntro (phi #> Not phi) d7
--    d9  <- assume (Not (phi #> Not phi) #> phi)
--    d10 <- implElim d8 d9
--    d11 <- implIntro (Not (Not phi)) d10
--    return d11

main :: IO ()
main = putStrLn "Hello, world!"
