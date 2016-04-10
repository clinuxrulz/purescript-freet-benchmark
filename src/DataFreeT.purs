-- | This module defines a stack-safe implementation of the _free monad transformer_.

module Main.DataFreeT
  ( FreeT()
  , freeT
  , liftFreeT
  , hoistFreeT
  , interpret
  , bimapFreeT
  , resume
  , runFreeT
  ) where

import Prelude

import Data.Either (Either(..), either)

import Control.Monad.Rec.Class (MonadRec, tailRecM)
import Control.Monad.Trans (MonadTrans, lift)

data FreeT_ f m a r
  = FreeT_
      (a -> r)
      (m a -> r)
      (f a -> r)
      ((Unit -> FreeT f m a) -> r)
      (forall b. FreeT f m b -> (b -> FreeT f m a) -> r)

-- | The free monad transformer for the functor `f`.
newtype FreeT f m a = FreeT (forall r. FreeT_ f m a r -> r)

done_ :: forall f m a. a -> FreeT f m a
done_ a = FreeT (\(FreeT_ x _ _ _ _) -> x a)

liftM_ :: forall f m a. m a -> FreeT f m a
liftM_ m = FreeT (\(FreeT_ _ x _ _ _) -> x m)

liftF_ :: forall f m a. f a -> FreeT f m a
liftF_ f = FreeT (\(FreeT_ _ _ x _ _) -> x f)

suspend_ :: forall f m a. (Unit -> FreeT f m a) -> FreeT f m a
suspend_ thunk = FreeT (\(FreeT_ _ _ _ x _) -> x thunk)

bind__ :: forall f m a b. FreeT f m a -> (a -> FreeT f m b) -> FreeT f m b
bind__ m f = FreeT (\(FreeT_ _ _ _ _ x) -> x m f)

bind_ :: forall f m a b. FreeT f m a -> (a -> FreeT f m b) -> FreeT f m b
bind_ m'@(FreeT m) f = m $
  FreeT_
    (\a -> f a)
    (\m2 -> bind__ m' f)
    (\f2 -> bind__ m' f)
    (\thunk -> bind__ m' f)
    (\m2 f2 -> bind__ m2 (\x -> bind__ (suspend_ (\_ -> f2 x)) f))

instance functorFreeT :: Functor (FreeT f m) where
  map f ma = bind_ ma (done_ <<< f)

instance applyFreeT :: Apply (FreeT f m) where
  apply mf ma = bind_ mf (\f -> bind_ ma (done_ <<< f))

instance applicativeFreeT :: Applicative (FreeT f m) where
  pure a = done_ a

instance bindFreeT :: Bind (FreeT f m) where
  bind = bind_

instance monadFreeT :: Monad (FreeT f m)

instance monadTransFreeT :: MonadTrans (FreeT f) where
  lift = liftM_

instance monadRecFreeT :: MonadRec (FreeT f m) where
  tailRecM go = go2
    where
      go2 a = (go a) >>= (
        either
          go2
          pure
      )

-- | Construct a computation of type `FreeT`.
freeT :: forall f m a. (Functor f, Monad m) => (Unit -> m (Either a (f (FreeT f m a)))) -> FreeT f m a
freeT thunk =
  suspend_ (\_ ->
    (lift $ thunk unit) >>= (
      either
        pure
        ((\x -> bind_ x id) <<< liftF_)
    )
  )

resumeStep :: forall f m a. (Functor f, MonadRec m) => FreeT_ f m a (m (Either (FreeT f m a) (Either a (f (FreeT f m a)))))
resumeStep =
  FreeT_
    (pure <<< Right <<< Left)
    ((Right <<< Left) <$> _)
    (pure <<< Right <<< Right <<< (pure <$> _))
    (\thunk -> pure $ Left $ thunk unit)
    (\(FreeT m2) f -> m2 $
      FreeT_
        (pure <<< Left <<< f)
        ((Left <<< f) <$> _)
        (pure <<< Right <<< Right <<< (f <$> _))
        (\thunk -> pure $ Left $ bind_ (thunk unit) f)
        (\m3 f2 -> pure $ Left $ (bind_ m3 (\a -> bind_ (f2 a) f)))
    )

-- | Unpack `FreeT`, exposing the first step of the computation.
resume :: forall f m a. (Functor f, MonadRec m) => FreeT f m a -> m (Either a (f (FreeT f m a)))
resume = tailRecM (go resumeStep)
  where
    go :: FreeT_ f m a (m (Either (FreeT f m a) (Either a (f (FreeT f m a)))))
       -> FreeT f m a
       -> m (Either (FreeT f m a) (Either a (f (FreeT f m a))))
    go resumeStep' (FreeT m) = m resumeStep'

-- | Lift an action from the functor `f` to a `FreeT` action.
liftFreeT :: forall f m a. f a -> FreeT f m a
liftFreeT = liftF_

-- | Change the underlying `Monad` for a `FreeT` action.
hoistFreeT :: forall f m n a. (Functor f, Monad m, Monad n) => (forall b. m b -> n b) -> FreeT f m a -> FreeT f n a
hoistFreeT = bimapFreeT id

-- | Change the base functor `f` for a `FreeT` action.
interpret :: forall f g m a. (Functor f, Functor g, Monad m) => (forall b. f b -> g b) -> FreeT f m a -> FreeT g m a
interpret nf = bimapFreeT nf id

-- | Change the base functor `f` and the underlying `Monad` for a `FreeT` action.
bimapFreeT :: forall f g m n a. (Functor f, Functor g, Monad m, Monad n) => (forall b. f b -> g b) -> (forall b. m b -> n b) -> FreeT f m a -> FreeT g n a
bimapFreeT fg mn (FreeT m) = m $
  FreeT_
    done_
    (\m -> liftM_ $ mn m)
    (\f -> liftF_ $ fg f)
    (\thunk -> suspend_ (\_ -> bimapFreeT fg mn (thunk unit)))
    (\m2 f -> bind_ (bimapFreeT fg mn m2) ((bimapFreeT fg mn) <<< f))

runFreeTStep :: forall f m a. (Functor f, MonadRec m) => (f (FreeT f m a) -> m (FreeT f m a)) -> FreeT_ f m a (m (Either (FreeT f m a) a))
runFreeTStep f =
  FreeT_
    (pure <<< Right)
    (Right <$> _)
    ((Left <$> _) <<< f <<< (pure <$> _))
    (\thunk -> pure $ Left $ thunk unit)
    (\(FreeT m2) f2 -> m2 $
      FreeT_
        (pure <<< Left <<< f2)
        ((Left <<< f2) <$> _)
        (\f3 -> Left <$> f (f2 <$> f3))
        (\thunk -> pure $ Left $ bind_ (thunk unit) f2)
        (\m3 f3 -> pure $ Left $ (bind_ m3 (\a -> bind_ (f3 a) f2)))
    )

-- | Run a `FreeT` computation to completion.
runFreeT :: forall f m a. (Functor f, MonadRec m) => (f (FreeT f m a) -> m (FreeT f m a)) -> FreeT f m a -> m a
runFreeT f = tailRecM (go (runFreeTStep f))
  where
    go :: FreeT_ f m a (m (Either (FreeT f m a) a))
       -> FreeT f m a
       -> m (Either (FreeT f m a) a)
    go runFreeTStep' (FreeT m) = m runFreeTStep'
