module Main where

import Main.OriginalFreeTe0a15ee as Orig
import Main.CodensityBasedFreeT as Cod
import Main.DataFreeT as Data
import Main.FreeT2 as V2

import Prelude
import Data.Array
import Data.Foldable
import Data.Monoid.Additive
import Data.Monoid.Multiplicative
import Data.Identity
import Control.Monad.Eff
import Control.Monad.Trans (lift)
import Test.QuickCheck.Arbitrary (arbitrary)
import Test.QuickCheck.Gen (vectorOf)
import Benchotron.Core
import Benchotron.UI.Console

leftBindLargeBenchmark :: Benchmark
leftBindLargeBenchmark = mkBenchmark
  { slug: "left-bind-large"
  , title: "Left associated binds (" ++ show inputsPerSize ++ " input per size)"
  , sizes: [1, 2, 3, 4, 5, 6] <#> (* 100000)
  , sizeInterpretation: "Number of binds"
  , inputsPerSize: inputsPerSize
  , gen: \n -> vectorOf n (pure 0.0)
  , functions: [ benchFn "Original FreeT" (runIdentity <<< (Orig.runFreeT id) <<< origBinds)
               --, benchFn "Rec CPS FreeT" (runIdentity <<< (Cod.runFreeT id) <<< codBinds)
               --, benchFn "Data CPS FreeT" (runIdentity <<< (Data.runFreeT id) <<< dataBinds)
               , benchFn "FreeT2" (runIdentity <<< (V2.runFreeT id) <<< v2Binds)
               ]
  }
  where
  inputsPerSize :: Int
  inputsPerSize = 1

  origBinds :: Array Number -> Orig.FreeT Identity Identity Number
  origBinds as = foldl (\b a -> b >>= const (origGen a)) (origGen 0.0) as

  origGen :: forall a. a -> Orig.FreeT Identity Identity a
  origGen = lift <<< pure

  codBinds :: Array Number -> Cod.FreeT Identity Identity Number
  codBinds as = foldl (\b a -> b >>= const (codGen a)) (codGen 0.0) as

  codGen :: forall a. a -> Cod.FreeT Identity Identity a
  codGen = lift <<< pure

  dataBinds :: Array Number -> Data.FreeT Identity Identity Number
  dataBinds as = foldl (\b a -> b >>= const (dataGen a)) (dataGen 0.0) as

  dataGen :: forall a. a -> Data.FreeT Identity Identity a
  dataGen = lift <<< pure

  v2Binds :: Array Number -> V2.FreeT Identity Identity Number
  v2Binds as = foldl (\b a -> b >>= const (v2Gen a)) (v2Gen 0.0) as

  v2Gen :: forall a. a -> V2.FreeT Identity Identity a
  v2Gen = lift <<< pure

rightBindLargeBenchmark :: Benchmark
rightBindLargeBenchmark = mkBenchmark
  { slug: "right-bind-large"
  , title: "Right associated binds (" ++ show inputsPerSize ++ " input per size)"
  , sizes: [1, 2, 3, 4, 5, 6] <#> (* 100000)
  , sizeInterpretation: "Number of binds"
  , inputsPerSize: inputsPerSize
  , gen: \n -> vectorOf n (pure 0.0)
  , functions: [ benchFn "Original FreeT" (runIdentity <<< (Orig.runFreeT id) <<< origBinds)
               --, benchFn "Rec CPS FreeT" (runIdentity <<< (Cod.runFreeT id) <<< codBinds)
               --, benchFn "Data CPS FreeT" (runIdentity <<< (Data.runFreeT id) <<< dataBinds)
               , benchFn "FreeT2" (runIdentity <<< (V2.runFreeT id) <<< v2Binds)
               ]
  }
  where
  inputsPerSize :: Int
  inputsPerSize = 1

  origBinds :: Array Number -> Orig.FreeT Identity Identity Number
  origBinds as = foldl (\b a -> origGen a >>= const b) (origGen 0.0) as

  origGen :: forall a. a -> Orig.FreeT Identity Identity a
  origGen = lift <<< pure

  codBinds :: Array Number -> Cod.FreeT Identity Identity Number
  codBinds as = foldl (\b a -> codGen a >>= const b) (codGen 0.0) as

  codGen :: forall a. a -> Cod.FreeT Identity Identity a
  codGen = lift <<< pure

  dataBinds :: Array Number -> Data.FreeT Identity Identity Number
  dataBinds as = foldl (\b a -> dataGen a >>= const b) (dataGen 0.0) as

  dataGen :: forall a. a -> Data.FreeT Identity Identity a
  dataGen = lift <<< pure

  v2Binds :: Array Number -> V2.FreeT Identity Identity Number
  v2Binds as = foldl (\b a -> v2Gen a >>= const b) (v2Gen 0.0) as

  v2Gen :: forall a. a -> V2.FreeT Identity Identity a
  v2Gen = lift <<< pure

main = runSuite [ leftBindLargeBenchmark
                , rightBindLargeBenchmark
                ]
