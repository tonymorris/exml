{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Xml.Parser where

import Control.Applicative
import Control.Lens(Optic, Choice, prism, set, over, (^?))
import Data.Bifunctor(Bifunctor(bimap))
import Data.Bool(bool)
import Data.Digit(Digit, digitC)
import Data.Functor.Alt(Alt((<!>)))
import Data.Functor.Apply(Apply((<.>)))
import Data.Functor.Bind(Bind((>>-)))
import Data.List.NonEmpty(NonEmpty((:|)), toList)
import Prelude

type Input =
  String

data Result e a =
  ErrorResult e
  | ValueResult Input a
  deriving (Eq, Ord, Show)  

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

newtype Parser s e a =
  Parser (Input -> s -> (s, Result e a))

instance Functor (Parser s e) where
  fmap f (Parser p) =
    Parser (\i s -> 
      let (t, r) = p i s
      in (t, fmap f r))

instance Apply (Parser s e) where
  Parser f <.> Parser a =
    Parser (\i s -> 
      let (t, r) = f i s          
      in case r of 
           ErrorResult e ->
             (t, ErrorResult e)
           ValueResult j g ->
             fmap (fmap (g$)) (a j t))

instance Applicative (Parser s e) where
  (<*>) =
    (<.>)
  pure a =
    Parser (\i s ->
      (s, ValueResult i a))

instance Bind (Parser s e) where
  Parser p >>- f =
    Parser (\i s -> 
      let (t, r) = p i s          
      in case r of 
           ErrorResult e ->
             (t, ErrorResult e)
           ValueResult j a ->
             let Parser q = f a 
             in q j t)

instance Monad (Parser s e) where
  (>>=) =
    (>>-)
  return =
    pure

instance Alt (Parser s e) where
  Parser p <!> Parser q =
    Parser (\i s -> 
      let (t, r) = p i s          
      in case r of 
           ErrorResult _ ->
             q i s
           ValueResult j a ->
             (t, ValueResult j a))

(.=.) ::
  e
  -> Parser s x a
  -> Parser s e a
e .=. Parser p =
  Parser (\i ->
    fmap (set _ErrorResult e) . p i)
  
infixl 6 .=.

(.~.) ::
  (x -> e)
  -> Parser s x a
  -> Parser s e a
e .~. Parser p =
  Parser (\i ->
    fmap (over _ErrorResult e) . p i)

infixl 6 .~.

class SemiCharState s where
  updateCharState ::
    Char
    -> s
    -> s

class SemiCharState s => CharState s where
  emptyCharState ::
    s
  
failed ::
  e
  -> Parser s e a
failed e =
  Parser (\_ s -> 
    (s, ErrorResult e))

character ::
  SemiCharState s =>
  Parser s () Char
character =
  Parser (\i s -> 
    case i of
      [] ->
        (s, ErrorResult ())
      h:t ->
        (updateCharState h s, ValueResult t h))

list ::
  Parser s e a
  -> Parser s e [a]
list p =
  fmap toList (list1 p) <!> pure []  


list1 ::
  Parser s e a
  -> Parser s e (NonEmpty a)
list1 p =
  do h <- p
     t <- list p
     return (h :| t)

satisfy ::
  SemiCharState s =>
  (Char -> Bool)
  -> Parser s Bool Char
satisfy f =
  do c <- True .=. character
     bool (failed False) (return c) (f c)

is ::
  SemiCharState s =>
  Char
  -> Parser s Bool Char
is c =
  satisfy (== c)

digit ::
  SemiCharState s =>
  Parser s Bool Digit
digit =
  do c <- True .=. character
     case c ^? digitC of
       Nothing ->
         failed False
       Just d ->
         return d
  