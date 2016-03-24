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
newtype InnerFreeT f m a = InnerFreeT (
  forall r. {
    pureFreeT :: a -> r,
    liftMFreeT :: m (InnerFreeT f m a) -> r,
    liftFFreeT :: f (InnerFreeT f m a) -> r,
    suspendFreeT :: (Unit -> InnerFreeT f m a) -> r
  }
  -> r
)

mapInnerFreeT_ :: forall f m a b. (Functor f, Functor m) => (a -> b) -> InnerFreeT f m a -> InnerFreeT f m b
mapInnerFreeT_ f m = m >>= (pure <<< f)

applyInnerFreeT_ :: forall f m a b. (Functor f, Functor m) => InnerFreeT f m (a -> b) -> InnerFreeT f m a -> InnerFreeT f m b
applyInnerFreeT_ mf ma = do
  f <- mf
  f <$> ma

suspend :: forall f m a. (Unit -> InnerFreeT f m a) -> InnerFreeT f m a
suspend thunk = InnerFreeT (\{ suspendFreeT } -> suspendFreeT thunk)

liftF :: forall f m a. f (InnerFreeT f m a) -> InnerFreeT f m a
liftF f = InnerFreeT (\{ liftFFreeT } -> liftFFreeT f)

liftM :: forall f m a. m (InnerFreeT f m a) -> InnerFreeT f m a
liftM m = InnerFreeT (\{ liftMFreeT } -> liftMFreeT m)

instance functorInnerFreeT :: (Functor f, Functor m) => Functor (InnerFreeT f m) where
  map = mapInnerFreeT_

instance applyInnerFreeT :: (Functor f, Functor m) => Apply (InnerFreeT f m) where
  apply mf ma = applyInnerFreeT_ mf ma

instance applicativeInnerFreeT :: (Functor f, Functor m) => Applicative (InnerFreeT f m) where
  pure a = InnerFreeT (\{ pureFreeT } -> pureFreeT a)

instance bindInnerFreeT :: (Functor f, Functor m) => Bind (InnerFreeT f m) where
  bind (InnerFreeT m) f =
    m {
      pureFreeT: (\a -> suspend (\_ -> f a)),
      liftMFreeT: (\m2 -> liftM $ ((_ >>= f) <$> m2)),
      liftFFreeT: (\f2 -> liftF ((_ >>= f) <$> f2)),
      suspendFreeT: (\thunk -> (thunk unit) >>= f)
    }

instance monadInnerFreeT :: (Functor f, Functor m) => Monad (InnerFreeT f m)

instance monadTransInnerFreeT :: (Functor f) => MonadTrans (InnerFreeT f) where
  lift m = InnerFreeT (\{ liftMFreeT } -> liftMFreeT (pure <$> m))

instance monadRecInnerFreeT :: (Functor f, Functor m) => MonadRec (InnerFreeT f m) where
  tailRecM go a = suspend (\_ ->
    (go a) >>= (
      either
        (tailRecM go)
        pure
    )
  )

newtype FreeT f m a = FreeT (forall r. (a -> InnerFreeT f m r) -> InnerFreeT f m r)

innerFreeTToFreeT :: forall f m a. (Functor f, Functor m) => InnerFreeT f m a -> FreeT f m a
innerFreeTToFreeT c = FreeT (c >>= _)

freeTToInnerFreeT :: forall f m a. (Functor f, Functor m) => FreeT f m a -> InnerFreeT f m a
freeTToInnerFreeT (FreeT c) = c pure

instance functorFreeT :: Functor (FreeT f m) where
  map f (FreeT c) = FreeT (\k -> suspend (\_ -> c (k <<< f)))

instance applyFreeT :: Apply (FreeT f m) where
  apply (FreeT cf) (FreeT ca) = FreeT (\k -> suspend (\_ -> cf (\f -> ca (k <<< f))))

instance applicativeFreeT :: Applicative (FreeT f m) where
  pure a = FreeT (_ $ a)

instance bindFreeT :: Bind (FreeT f m) where
  bind (FreeT ca) f = FreeT (\k -> suspend (\_ -> ca (\a -> case f a of FreeT c -> c k)))

instance monadFreeT :: Monad (FreeT f m)

instance monadTransFreeT :: (Functor f) => MonadTrans (FreeT f) where
  lift m = FreeT (\k -> (lift m) >>= k)

instance monadRecFreeT :: (Functor f, Functor m) => MonadRec (FreeT f m) where
  tailRecM go a = innerFreeTToFreeT $ tailRecM (freeTToInnerFreeT <<< go) a

-- | Construct a computation of type `FreeT`.
freeT :: forall f m a. (Functor f, Monad m) => (Unit -> m (Either a (f (FreeT f m a)))) -> FreeT f m a
freeT thunk =
  innerFreeTToFreeT $
    (lift (thunk unit)) >>= (
      either
        pure
        (\f -> liftF $ freeTToInnerFreeT <$> f)
    )

resumeStep :: forall f m a. (Functor f, Monad m) => {
  pureFreeT :: a -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a)))),
  liftMFreeT :: m (InnerFreeT f m a) -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a)))),
  liftFFreeT :: f (InnerFreeT f m a) -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a)))),
  suspendFreeT :: (Unit -> InnerFreeT f m a) -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a))))
}
resumeStep = {
  pureFreeT: (\a -> return $ Right $ Left a),
  liftMFreeT: (\m -> Left <$> m),
  liftFFreeT: (\f -> return $ Right $ Right $ innerFreeTToFreeT <$> f),
  suspendFreeT: (\thunk -> return $ Left $ thunk unit)
}

resume :: forall f m a. (Functor f, MonadRec m) => FreeT f m a -> m (Either a (f (FreeT f m a)))
resume = (tailRecM (go resumeStep)) <<< freeTToInnerFreeT
  where
    go :: {
            pureFreeT :: a -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a)))),
            liftMFreeT :: m (InnerFreeT f m a) -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a)))),
            liftFFreeT :: f (InnerFreeT f m a) -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a)))),
            suspendFreeT :: (Unit -> InnerFreeT f m a) -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a))))
          }
       -> InnerFreeT f m a
       -> m (Either (InnerFreeT f m a) (Either a (f (FreeT f m a))))
    go step (InnerFreeT free) = free step

-- | Lift an action from the functor `f` to a `FreeT` action.
liftFreeT :: forall f m a. (Functor f, Monad m) => f a -> FreeT f m a
liftFreeT fa = innerFreeTToFreeT $ InnerFreeT (\{ liftFFreeT } -> liftFFreeT $ pure <$> fa)

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
