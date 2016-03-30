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
    done :: a -> r,
    liftM :: m (FreeT f m a) -> r,
    liftF :: f (FreeT f m a) -> r,
    bind :: forall b. FreeT f m b -> (b -> FreeT f m a) -> r
  }
  -> r
)

done_ :: forall f m a. a -> FreeT f m a
done_ a = FreeT (\{ done: x } -> x a)

liftM_ :: forall f m a. m (FreeT f m a) -> FreeT f m a
liftM_ m = FreeT (\{ liftM: x } -> x m)

liftF_ :: forall f m a. f (FreeT f m a) -> FreeT f m a
liftF_ f = FreeT (\{ liftF: x } -> x f)

bind_ :: forall f m a b. FreeT f m a -> (a -> FreeT f m b) -> FreeT f m b
bind_ (FreeT m) f = m {
  done: (\a -> f a),
  liftM: (\m2 -> bind_ (liftM_ m2) f),
  liftF: (\f2 -> bind_ (liftF_ f2) f),
  bind: (\m2 f2 -> bind_ m2 (\a -> bind_ (f2 a) f))
}

instance functorFreeT :: Functor (FreeT f m) where
  map f (FreeT m) = m {
    done: (\a -> done_ $ f a),
    liftM: (\m2 -> bind_ (liftM_ m2) (done_ <<< f)),
    liftF: (\f2 -> bind_ (liftF_ f2) (done_ <<< f)),
    bind: (\m2 f2 -> bind_ m2 (\a -> bind_ (f2 a) (done_ <<< f)))
  }

instance applyFreeT :: Apply (FreeT f m) where
  apply mf ma = bind_ mf (\f -> bind_ ma (done_ <<< f))

instance applicativeFreeT :: Applicative (FreeT f m) where
  pure a = done_ a

instance bindFreeT :: Bind (FreeT f m) where
  bind = bind_

instance monadFreeT :: Monad (FreeT f m)

instance monadTransFreeT :: MonadTrans (FreeT f) where
  lift = liftM_ <<< (map pure)

instance monadRecFreeT :: MonadRec (FreeT f m) where
  tailRecM go a =
    let again = tailRecM go
    in
    (go a) >>= (
      either
        again
        pure
    )

-- | Construct a computation of type `FreeT`.
freeT :: forall f m a. (Functor f, Monad m) => (Unit -> m (Either a (f (FreeT f m a)))) -> FreeT f m a
freeT thunk =
  (pure unit) >>= (\_ ->
    (lift $ thunk unit) >>= (
      either
        pure
        liftF_
    )
  )

resume :: forall f m a. (Functor f, MonadRec m) => FreeT f m a -> m (Either a (f (FreeT f m a)))
resume = tailRecM go
  where
    go :: FreeT f m a -> m (Either (FreeT f m a) (Either a (f (FreeT f m a))))
    go (FreeT m) = m {
      done: pure <<< Right <<< Left,
      liftM: (Left <$> _),
      liftF: pure <<< Right <<< Right,
      bind: (\m2 f ->
        (resume m2) >>= (
          either
            (pure <<< Left <<< f)
            (pure <<< Left <<< (\x -> bind_ (liftF_ x) f))
        )
      )
    }

-- | Lift an action from the functor `f` to a `FreeT` action.
liftFreeT :: forall f m a. (Functor f, Monad m) => f a -> FreeT f m a
liftFreeT = liftF_ <<< (pure <$> _)

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
