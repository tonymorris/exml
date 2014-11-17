{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Xml.Parser where

import Control.Applicative
import Control.Lens(Optic, Choice, prism)
import Control.Monad(ap)
import Data.Bifunctor
import Data.Functor.Apply
import Data.Functor.Bind
import Prelude

type Input =
  String

data Result e a =
  ErrorResult e
  | ValueResult Input a
  deriving (Eq, Ord)  

instance Functor (Result e) where
  fmap _ (ErrorResult e) =
    ErrorResult e
  fmap f (ValueResult s a) =
    ValueResult s (f a)      

instance Bifunctor Result where
  bimap f _ (ErrorResult e) =
    ErrorResult (f e)
  bimap _ g (ValueResult s a) =
    ValueResult s (g a)

class AsErrorResult p f x where
  _ErrorResult ::
    Optic p f (x e a) (x z a) e z

instance (Choice p, Applicative f) => AsErrorResult p f Result where
  _ErrorResult = 
    prism
      ErrorResult
      (\r -> case r of
               ErrorResult e ->
                 Right e
               ValueResult s a ->
                 Left (ValueResult s a))

class AsValueResult p f x where
  _ValueResult ::
    Optic p f (x e a) (x e b) (String, a) (String, b)

instance (Choice p, Applicative f) => AsValueResult p f Result where
  _ValueResult =
    prism
      (uncurry ValueResult)      
      (\r -> case r of
               ErrorResult e ->
                 Left (ErrorResult e)
               ValueResult s a ->
                 Right (s, a))

data ResultT e f a =
  ResultT
    (f (Result e a))

instance Functor f => Functor (ResultT e f) where
  fmap f (ResultT x) =
    ResultT (fmap (fmap f) x)

newtype Parser e f a =
  Parser
    (Input -> ResultT e f a)

instance (Functor f, Monad f) => Functor (Parser e f) where
  fmap f (Parser p) =
    Parser (fmap f . p)

instance (Functor f, Monad f) => Applicative (Parser e f) where
  pure =
    return
  (<*>) =
    ap

instance (Functor f, Monad f) => Apply (Parser e f) where
  (<.>) =
    (<*>)

instance (Functor f, Monad f) => Bind (Parser e f) where
  (>>-) =
    (>>=)

instance (Functor f, Monad f) => Monad (Parser e f) where
  return a =
    Parser (\i -> ResultT . return . ValueResult i $ a)
  Parser p >>= f =
    Parser (\i -> let ResultT r = p i
                  in ResultT (r >>= \s -> case s of
                                            ErrorResult e ->
                                              return (ErrorResult e)
                                            ValueResult j a ->
                                              let Parser q = f a
                                                  ResultT t = q j
                                              in t))
