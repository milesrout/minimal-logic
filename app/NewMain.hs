{-# LANGUAGE PartialTypeSignatures #-}

module Equivalences where

import Control.Monad
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)

import Minimal

dneImplAristotle :: Deduction f (f _)
dneImplAristotle = do
    let phi = Prop "phi"
    dNP   <- assume (Not phi)
    dPNP  <- implIntro phi dNP
    dNPNP <- assume (Not (phi #> Not phi))
    dBot  <- implElim dNPNP dPNP
    dNNP  <- implIntro (Not phi) dBot
    dDNE  <- assume ((Not (Not phi)) #> phi)
    dP    <- implElim dDNE dNNP
    implIntro (Not (phi #> Not phi)) dP

aristotleImplDne :: Deduction f (f _)
aristotleImplDne = do
    let phi = Prop "phi"
    dP     <- assume phi
    dPNP   <- assume (phi #> Not phi)
    dNP    <- implElim dPNP dP
    dNNP   <- assume (Not (Not phi))
    dBot   <- implElim dNNP dNP
    dNP'   <- implIntro phi dBot
    dBot'  <- implElim dNNP dNP'
    dNPNP  <- implIntro (phi #> Not phi) dBot'
    dNPNPP <- assume (Not (phi #> Not phi) #> phi)
    dP     <- implElim dNPNPP dNPNP
    dDNE   <- implIntro (Not (Not phi)) dP
    return dDNE

main :: IO ()
main = putStrLn "Hello, world!"
