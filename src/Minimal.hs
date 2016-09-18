{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Minimal where

import Control.Monad.Free
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Void
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

data DeductionF f next where
    Assume     :: Formula a -> (f a -> next) -> DeductionF f next
    ImplElim   :: f (a -> b) -> f a -> (f b -> next) -> DeductionF f next
    ImplIntro  :: Formula a -> f b -> (f (a -> b) -> next) -> DeductionF f next
    ConjIntro  :: f a -> f b -> (f (a,b) -> next) -> DeductionF f next
    ConjElimL  :: f (a,b) -> (f b -> next) -> DeductionF f next
    ConjElimR  :: f (a,b) -> (f a -> next) -> DeductionF f next
    DisjIntroL :: f a -> Formula b -> (f (Either a b) -> next) -> DeductionF f next
    DisjIntroR :: Formula a -> f b -> (f (Either a b) -> next) -> DeductionF f next
    DisjElim   :: f (Either a b) -> f (a -> c) -> f (b -> c) -> (f c -> next) -> DeductionF f next

-- We cannot use -XDeriveFunctor to generate this automatically, as DeductionF
-- is a generalised algebraic data type (GADT).
instance Functor (DeductionF f) where
    fmap f (Assume p g) = Assume p (f . g)
    fmap f (ImplElim ab a g) = ImplElim ab a (f . g)
    fmap f (ImplIntro a b g) = ImplIntro a b (f . g)
    fmap f (ConjIntro a b g) = ConjIntro a b (f . g)
    fmap f (ConjElimL ab g) = ConjElimL ab (f . g)
    fmap f (ConjElimR ab g) = ConjElimR ab (f . g)
    fmap f (DisjIntroL a q g) = DisjIntroL a q (f . g)
    fmap f (DisjIntroR p b g) = DisjIntroR p b (f . g)
    fmap f (DisjElim ab ac bc g) = DisjElim ab ac bc (f . g)

type Deduction f = Free (DeductionF f)

assume :: Formula a -> Deduction f (f a)
assume p = liftF (Assume p id)

implElim :: f (a -> b) -> f a -> Deduction f (f b)
implElim ab a = liftF (ImplElim ab a id)

implIntro :: Formula a -> f b -> Deduction f (f (a -> b))
implIntro a b = liftF (ImplIntro a b id)

conjIntro :: f a -> f b -> Deduction f (f (a,b))
conjIntro a b = liftF (ConjIntro a b id)

conjElimL :: f (a,b) -> Deduction f (f b)
conjElimL ab = liftF (ConjElimL ab id)

conjElimR :: f (a,b) -> Deduction f (f a)
conjElimR ab = liftF (ConjElimR ab id)

disjIntroL :: f a -> Formula b -> Deduction f (f (Either a b))
disjIntroL a q = liftF (DisjIntroL a q id)

disjIntroR :: Formula a -> f b -> Deduction f (f (Either a b))
disjIntroR p b = liftF (DisjIntroR p b id)

disjElim :: f (Either a b) -> f (a -> c) -> f (b -> c) -> Deduction f (f c)
disjElim ab ac bc = liftF (DisjElim ab ac bc id)

data Proof a = Proof { assumptions :: Set AnyFormula
                     , conclusion  :: Formula a
                     } deriving Show

data AnyFormula = forall a. MkAF (Formula a)

instance Ord AnyFormula where
    x <= y = show x <= show y

instance Eq AnyFormula where
    x == y = show x == show y

instance Show AnyFormula where
    show (MkAF f) = show f

interpret :: Deduction Proof (Proof a) -> Proof a
interpret (Pure x) = x
interpret (Free deduction) = case deduction of
    (Assume f g)             -> interpret . g $ Proof (Set.singleton (MkAF f)) f
    (ImplIntro fA dB g)      -> interpret . g $ Proof (Set.delete (MkAF fA) aB) (fA #> cB)
        where aB = assumptions dB
              cB = conclusion dB
    (ImplElim dAB dA g)      -> interpret . g $ Proof (Set.union aAB aA) fB
        where fB = case conclusion dAB of
                (Impl _ b)   -> b
              aAB = assumptions dAB
              aA = assumptions dA
    (ConjIntro dA dB g)      -> interpret . g $ Proof (Set.union aA aB) (fA #& fB)
        where aA = assumptions dA
              aB = assumptions dB
              fA = conclusion dA
              fB = conclusion dB
    (ConjElimL dAB g)        -> interpret . g $ Proof aAB fB
        where aAB = assumptions dAB
              fB = case conclusion dAB of
                (Conj _ b) -> b
    (ConjElimR dAB g)        -> interpret . g $ Proof aAB fA
        where aAB = assumptions dAB
              fA = case conclusion dAB of
                (Conj a _) -> a
    (DisjIntroL dA fQ g)     -> interpret . g $ Proof aA (fA #| fQ)
        where aA = assumptions dA
              fA = conclusion dA
    (DisjIntroR fP dB g)     -> interpret . g $ Proof aB (fP #| fB)
        where aB = assumptions dB
              fB = conclusion dB
    (DisjElim dAB dAC dBC g) -> interpret . g $ Proof aC fC
        where aAB = assumptions dAB
              aAC = assumptions dAC
              aBC = assumptions dBC
              aC = Set.unions [aAB,aAC,aBC]
              fC = case conclusion dAC of
                (Impl _ c) -> c

blah :: Deduction f (f ())
blah = do
    dP <- assume (q #> p)
    dQ <- assume q
    implElim dP dQ
