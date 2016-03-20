module Main where

import Main.OriginalFreeTe0a15ee as Orig
import Main.CodensityBasedFreeT7dc0bc0 as Cod

import Prelude
import Data.Array
import Data.Foldable
import Data.Monoid.Additive
import Data.Monoid.Multiplicative
import Data.Identity
import Control.Monad.Eff
import Test.QuickCheck.Arbitrary (arbitrary)
import Test.QuickCheck.Gen (vectorOf)
import Benchotron.Core
import Benchotron.UI.Console

leftBindLargeBenchmark :: Benchmark
leftBindLargeBenchmark = mkBenchmark
  { slug: "left-bind-large"
  , title: "Left associated binds (" ++ show inputsPerSize ++ " input per size)"
  , sizes: [1, 2, 3, 4, 5, 6, 7] <#> (* 100000)
  , sizeInterpretation: "Number of binds"
  , inputsPerSize: inputsPerSize
  , gen: \n -> vectorOf n (pure 0.0)
  , functions: [ benchFn "Original FreeT" (runIdentity <<< (Orig.runFreeT id) <<< origBinds)
               , benchFn "Codensity FreeT" (runIdentity <<< (Cod.runFreeT id) <<< codBinds)
               ]
  }
  where
  inputsPerSize :: Int
  inputsPerSize = 1

  origBinds :: Array Number -> Orig.FreeT Identity Identity Number
  origBinds as = foldl (\b a -> b >>= const (origGen a)) (origGen 0.0) as

  origGen :: forall a. a -> Orig.FreeT Identity Identity a
  origGen = pure

  codBinds :: Array Number -> Cod.FreeT Identity Identity Number
  codBinds as = foldl (\b a -> b >>= const (codGen a)) (codGen 0.0) as

  codGen :: forall a. a -> Cod.FreeT Identity Identity a
  codGen = pure

rightBindLargeBenchmark :: Benchmark
rightBindLargeBenchmark = mkBenchmark
  { slug: "right-bind-large"
  , title: "Right associated binds (" ++ show inputsPerSize ++ " input per size)"
  , sizes: [1, 2, 3, 4, 5, 6, 7] <#> (* 100000)
  , sizeInterpretation: "Number of binds"
  , inputsPerSize: inputsPerSize
  , gen: \n -> vectorOf n (pure 0.0)
  , functions: [ benchFn "Original FreeT" (runIdentity <<< (Orig.runFreeT id) <<< origBinds)
               , benchFn "Codensity FreeT" (runIdentity <<< (Cod.runFreeT id) <<< codBinds)
               ]
  }
  where
  inputsPerSize :: Int
  inputsPerSize = 1

  origBinds :: Array Number -> Orig.FreeT Identity Identity Number
  origBinds as = foldl (\b a -> origGen a >>= const b) (origGen 0.0) as

  origGen :: forall a. a -> Orig.FreeT Identity Identity a
  origGen = pure

  codBinds :: Array Number -> Cod.FreeT Identity Identity Number
  codBinds as = foldl (\b a -> codGen a >>= const b) (codGen 0.0) as

  codGen :: forall a. a -> Cod.FreeT Identity Identity a
  codGen = pure

main = runSuite [ leftBindLargeBenchmark
                , rightBindLargeBenchmark
                ]
