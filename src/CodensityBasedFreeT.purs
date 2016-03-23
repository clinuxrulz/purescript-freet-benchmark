-- | This module defines a stack-safe implementation of the _free monad transformer_.

module Main.CodensityBasedFreeT
  ( FreeT()
  , freeT
  , liftFreeT
  {-
  , hoistFreeT
  , interpret
  , bimapFreeT
  -}
  , resume
  , runFreeT
  ) where

import Prelude

import Data.Either (Either(..), either)

import Control.Monad.Rec.Class (MonadRec, tailRecM)
import Control.Monad.Trans (MonadTrans, lift)
import Unsafe.Coerce

-- | The free monad transformer for the functor `f`.
newtype FreeT f m a = FreeT (
  forall r. {
    pureFreeT :: a -> r,
    liftMFreeT :: m (FreeT f m a) -> r,
    liftFFreeT :: f (FreeT f m a) -> r,
    suspendFreeT :: (Unit -> FreeT f m a) -> r
  }
  -> r
)

mapFreeT_ :: forall f m a b. (Functor f, Functor m) => (a -> b) -> FreeT f m a -> FreeT f m b
mapFreeT_ f m = m >>= (pure <<< f)

applyFreeT_ :: forall f m a b. (Functor f, Functor m) => FreeT f m (a -> b) -> FreeT f m a -> FreeT f m b
applyFreeT_ mf ma = do
  f <- mf
  f <$> ma

suspend :: forall f m a. (Unit -> FreeT f m a) -> FreeT f m a
suspend thunk = FreeT (\{ suspendFreeT } -> suspendFreeT thunk)

liftF :: forall f m a. f (FreeT f m a) -> FreeT f m a
liftF f = FreeT (\{ liftFFreeT } -> liftFFreeT f)

liftM :: forall f m a. m (FreeT f m a) -> FreeT f m a
liftM m = FreeT (\{ liftMFreeT } -> liftMFreeT m)

instance functorFreeT :: (Functor f, Functor m) => Functor (FreeT f m) where
  map = mapFreeT_

instance applyFreeT :: (Functor f, Functor m) => Apply (FreeT f m) where
  apply mf ma = applyFreeT_ mf ma

instance applicativeFreeT :: (Functor f, Functor m) => Applicative (FreeT f m) where
  pure a = FreeT (\{ pureFreeT } -> pureFreeT a)

instance bindFreeT :: (Functor f, Functor m) => Bind (FreeT f m) where
  bind (FreeT m) f =
    m {
      pureFreeT: (\a -> suspend (\_ -> f a)),
      liftMFreeT: (\m2 -> liftM $ ((_ >>= f) <$> m2)),
      liftFFreeT: (\f2 -> liftF ((_ >>= f) <$> f2)),
      suspendFreeT: (\thunk -> (thunk unit) >>= f)
    }

instance monadFreeT :: (Functor f, Functor m) => Monad (FreeT f m)

instance monadTransFreeT :: (Functor f) => MonadTrans (FreeT f) where
  lift m = FreeT (\{ liftMFreeT } -> liftMFreeT (pure <$> m))

instance monadRecFreeT :: (Functor f, Functor m) => MonadRec (FreeT f m) where
  tailRecM go a = suspend (\_ ->
    (go a) >>= (
      either
        (tailRecM go)
        pure
    )
  )

-- | Construct a computation of type `FreeT`.
freeT :: forall f m a. (Functor f, Monad m) => (Unit -> m (Either a (f (FreeT f m a)))) -> FreeT f m a
freeT thunk =
  (lift (thunk unit)) >>= (
    either
      pure
      liftF
  )

resumeStep :: forall f m a. (Functor f, Monad m) => {
  pureFreeT :: a -> m (Either (FreeT f m a) (Either a (f (FreeT f m a)))),
  liftMFreeT :: m (FreeT f m a) -> m (Either (FreeT f m a) (Either a (f (FreeT f m a)))),
  liftFFreeT :: f (FreeT f m a) -> m (Either (FreeT f m a) (Either a (f (FreeT f m a)))),
  suspendFreeT :: (Unit -> FreeT f m a) -> m (Either (FreeT f m a) (Either a (f (FreeT f m a))))
}
resumeStep = {
  pureFreeT: (\a -> return $ Right $ Left a),
  liftMFreeT: (\m -> Left <$> m),
  liftFFreeT: (\f -> (pure <<< Right <<< Right) f),
  suspendFreeT: (\thunk -> return $ Left $ thunk unit)
}

resume :: forall f m a. (Functor f, MonadRec m) => FreeT f m a -> m (Either a (f (FreeT f m a)))
resume = tailRecM (go resumeStep)
  where
    go :: {
            pureFreeT :: a -> m (Either (FreeT f m a) (Either a (f (FreeT f m a)))),
            liftMFreeT :: m (FreeT f m a) -> m (Either (FreeT f m a) (Either a (f (FreeT f m a)))),
            liftFFreeT :: f (FreeT f m a) -> m (Either (FreeT f m a) (Either a (f (FreeT f m a)))),
            suspendFreeT :: (Unit -> FreeT f m a) -> m (Either (FreeT f m a) (Either a (f (FreeT f m a))))
          }
       -> FreeT f m a
       -> m (Either (FreeT f m a) (Either a (f (FreeT f m a))))
    go step (FreeT free) = free step

-- | Lift an action from the functor `f` to a `FreeT` action.
liftFreeT :: forall f m a. (Functor f, Monad m) => f a -> FreeT f m a
liftFreeT fa = FreeT (\{ liftFFreeT } -> liftFFreeT $ pure <$> fa)

{-
-- | Change the underlying `Monad` for a `FreeT` action.
hoistFreeT :: forall f m n a. (Functor f, Monad m, Monad n) => (forall b. m b -> n b) -> FreeT f m a -> FreeT f n a
hoistFreeT = bimapFreeT id

-- | Change the base functor `f` for a `FreeT` action.
interpret :: forall f g m a. (Functor f, Functor g, Monad m) => (forall b. f b -> g b) -> FreeT f m a -> FreeT g m a
interpret nf = bimapFreeT nf id

-- | Change the base functor `f` and the underlying `Monad` for a `FreeT` action.
bimapFreeT :: forall f g m n a. (Functor f, Functor g, Monad m, Monad n) => (forall b. f b -> g b) -> (forall b. m b -> n b) -> FreeT f m a -> FreeT g n a
bimapFreeT fg mn (FreeT c) = FreeT (\k -> suspTBind (bimapSuspT fg mn (c done)) k)
-}

-- | Run a `FreeT` computation to completion.
runFreeT :: forall f m a. (Functor f, MonadRec m) => (f (FreeT f m a) -> m (FreeT f m a)) -> FreeT f m a -> m a
runFreeT f = tailRecM go
  where
    go :: FreeT f m a -> m (Either (FreeT f m a) a)
    go free =
      (resume free) >>= (
        either
          (pure <<< Right)
          ((Left <$> _) <<< f)
      )
