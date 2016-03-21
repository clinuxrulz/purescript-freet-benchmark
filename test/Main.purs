module Test.Main where

import Main.Coroutine

import Prelude

import Data.Maybe
import Data.Either
import Data.Functor (($>))

import Control.Monad.Eff
import Control.Monad.Eff.Console
import Control.Monad.Trans
import Control.Monad.Rec.Class

nats :: forall m. (Monad m) => Producer Int m Unit
nats = go 0
  where
  go i = do
    emit i
    go (i + 1)

printer :: forall a. Consumer String (Eff _) Unit
printer = consumer \s -> log s $> Nothing

showing :: forall a m. (Show a, Monad m) => Transformer a String m Unit
showing = forever (transform show)

main = runProcess (nats $~ showing $$ printer)
