{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Minimal where

import Control.Monad.Free
import Text.Printf

data Formula a where
    Prop :: String -> Formula ()
    Impl :: Formula a -> Formula b -> Formula (a -> b)
    Conj :: Formula a -> Formula b -> Formula (a,b)
    Disj :: Formula a -> Formula b -> Formula (Either a b)

instance Show (Formula a) where
    show (Prop s)   = s
    show (Not f)    = printf "\x00AC%s" (show f)
    show (Conj a b) = printf "(%s \x2227 %s)" (show a) (show b)
    show (Disj a b) = printf "(%s \x2228 %s)" (show a) (show b)
    show (Impl a b) = printf "(%s \x2192 %s)" (show a) (show b)

a = Prop "A"
b = Prop "A"
p = Prop "P"
q = Prop "Q"

a #> b = Impl a b
a #& b = Conj a b
a #| b = Disj a b

pattern Bot = Prop "\x0020"
pattern Not a = Impl a Bot

data DeductionF next where
    Assume     :: Formula a -> (a -> next) -> DeductionF next
    ImplElim   :: (a -> b) -> a -> (b -> next) -> DeductionF next
    ImplIntro  :: b -> Formula a -> ((a -> b) -> next) -> DeductionF next
    ConjIntro  :: a -> b -> ((a,b) -> next) -> DeductionF next
    ConjElimL  :: (a,b) -> (b -> next) -> DeductionF next
    ConjElimR  :: (a,b) -> (a -> next) -> DeductionF next
    DisjIntroL :: a -> Formula b -> (Either a b -> next) -> DeductionF next
    DisjIntroR :: Formula a -> b -> (Either a b -> next) -> DeductionF next
    DisjElim   :: Either a b -> (a -> c) -> (b -> c) -> (c -> next) -> DeductionF next

-- We cannot use -XDeriveFunctor to generate this automatically, as DeductionF
-- is a generalised algebraic data type (GADT).
instance Functor DeductionF where
    fmap f (Assume p g) = Assume p (f . g)
    fmap f (ImplElim ab a g) = ImplElim ab a (f . g)
    fmap f (ImplIntro b a g) = ImplIntro b a (f . g)
    fmap f (ConjIntro a b g) = ConjIntro a b (f . g)
    fmap f (ConjElimL ab g) = ConjElimL ab (f . g)
    fmap f (ConjElimR ab g) = ConjElimR ab (f . g)
    fmap f (DisjIntroL a q g) = DisjIntroL a q (f . g)
    fmap f (DisjIntroR a q g) = DisjIntroR a q (f . g)
    fmap f (DisjElim ab ac bc g) = DisjElim ab ac bc (f . g)

type Deduction = Free DeductionF

assume :: Formula a -> Deduction a
assume p = liftF (Assume p id)

implElim :: (a -> b) -> a -> Deduction b
implElim ab a = liftF (ImplElim ab a id)

implIntro :: b -> Formula a -> Deduction (a -> b)
implIntro b a = liftF (ImplIntro b a id)

conjIntro :: a -> b -> Deduction (a,b)
conjIntro a b = liftF (ConjIntro a b id)

conjElimL :: (a,b) -> Deduction b
conjElimL ab = liftF (ConjElimL ab id)

conjElimR :: (a,b) -> Deduction a
conjElimR ab = liftF (ConjElimR ab id)

disjIntroL :: a -> Formula b -> Deduction (Either a b)
disjIntroL a q = liftF (DisjIntroL a q id)

disjIntroR :: Formula a -> b -> Deduction (Either a b)
disjIntroR a q = liftF (DisjIntroR a q id)

disjElim :: Either a b -> (a -> c) -> (b -> c) -> Deduction c
disjElim ab ac bc = liftF (DisjElim ab ac bc id)

blah = do
    let p = Prop "P"
    let q = Prop "Q"
    dP <- assume p
    dQ <- assume q
    dPQ <- conjIntro dP dQ
    return dPQ
