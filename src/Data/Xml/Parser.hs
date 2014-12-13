{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Xml.Parser where

import Control.Applicative
import Control.Lens(Optic, Optic', Choice, prism, set, over, (^?))
import Data.Bifunctor(Bifunctor(bimap))
import Data.Bool(bool)
import Data.Digit(Digit, digitC)
import Data.Functor.Alt(Alt((<!>)))
import Data.Functor.Apply(Apply((<.>)))
import Data.Functor.Bind(Bind((>>-)))
import Data.List.NonEmpty(NonEmpty((:|)), toList)
import Data.Traversable(Traversable(traverse))
import Data.Void(Void)
import Prelude8

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
  
instance SemiCharState () where
  updateCharState _ () =
    ()

class SemiCharState s => CharState s where
  emptyCharState ::
    s

instance CharState () where
  emptyCharState =
    ()

failed ::
  e
  -> Parser s e a
failed e =
  Parser (\_ s -> 
    (s, ErrorResult e))

data UnexpectedEofOr a =
  UnexpectedEof
  | UnexpectedEofOr a
  deriving (Eq, Ord, Show)

class AsUnexpectedEof p f x where
  _UnexpectedEof ::
    Optic' p f (x a) ()

instance (Choice p, Applicative f) => AsUnexpectedEof p f UnexpectedEofOr where
  _UnexpectedEof =
    prism
      (\() -> UnexpectedEof)
      (\e -> case e of
               UnexpectedEof ->
                 Right ()
               UnexpectedEofOr a ->
                 Left (UnexpectedEofOr a))

class AsUnexpectedEofOr p f x where
  _UnexpectedEofOr ::
    Optic p f (x a) (x b) a b

instance (Choice p, Applicative f) => AsUnexpectedEofOr p f UnexpectedEofOr where
  _UnexpectedEofOr =
    prism
      UnexpectedEofOr
      (\e -> case e of
               UnexpectedEof ->
                 Left UnexpectedEof
               UnexpectedEofOr a ->
                 Right a)

character ::
  SemiCharState s =>
  Parser s (UnexpectedEofOr Void) Char
character =
  Parser (\i s -> 
    case i of
      [] ->
        (s, ErrorResult UnexpectedEof)
      h:t ->
        (updateCharState h s, ValueResult t h))

list ::
  Parser s e a
  -- ?always succeeds -- new parser type?
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

data NotSatisfied =
  NotSatisfied (Char -> Bool) Char

satisfy ::
  SemiCharState s =>
  (Char -> Bool)
  -> Parser s (UnexpectedEofOr NotSatisfied) Char
satisfy f =
  do c <- UnexpectedEof .=. character
     bool (failed (UnexpectedEofOr (NotSatisfied f c))) (return c) (f c)

data NotIs =
  NotIs Char Char
  deriving (Eq, Ord, Show)

is ::
  SemiCharState s =>
  Char
  -> Parser s (UnexpectedEofOr NotIs) Char
is c =
  over _UnexpectedEofOr (\(NotSatisfied _ x) -> NotIs x c) .~. satisfy (== c)

string ::
  SemiCharState s =>
  String
  -> Parser s (UnexpectedEofOr NotIs) String
string =
  traverse is

data NotDigit =
  NotDigit Char
  deriving (Eq, Ord, Show)

digit ::
  SemiCharState s =>
  Parser s (UnexpectedEofOr NotDigit) Digit
digit =
  do c <- UnexpectedEof .=. character
     case c ^? digitC of
       Nothing ->
         failed (UnexpectedEofOr (NotDigit c))
       Just d ->
         return d
  
data Space =
  Space -- 0x0020
  | LineFeed -- 0x000a
  | CarriageReturn -- 0x000d
  | Tab -- 0x0009
  | Ideographic -- 0x3000
  deriving (Eq, Ord, Show)

data NotSpace =
  NotSpace Char
  deriving (Eq, Ord, Show)

space ::
  SemiCharState s =>
  Parser s (UnexpectedEofOr NotSpace) Space
space =
  do c <- UnexpectedEof .=. character
     case c of
       '\x0020' ->
         return Space
       '\x000a' ->
         return LineFeed
       '\x000d' ->
         return CarriageReturn
       '\x0009' ->
         return Tab
       '\x3000' ->
         return Ideographic
       _ ->
         failed (UnexpectedEofOr (NotSpace c))

{-
Error types
* UnexpectedEof ~ ()
* UnexpectedEofOrChar ~ Maybe Char
* UnexpectedEofOrCharAnd a ~ Maybe (Char, a)

-}

