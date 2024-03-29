{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module ResultT where
import Control.Monad.Trans
import Control.Monad.State

newtype ResultT m a = ResultT (m (Either String a))

runResultT :: ResultT m a -> m (Either String a)
runResultT (ResultT m) = m

instance Functor m => Functor (ResultT m) where
    fmap f (ResultT m) = ResultT (fmap (fmap f) m)
instance Applicative m => Applicative (ResultT m) where
    pure a = ResultT (pure (Right a))
    (<*>) (ResultT mf) (ResultT ma) = ResultT (fmap (<*>) mf <*> ma)
instance Monad m => Monad (ResultT m) where
    (>>=) (ResultT m) mf = ResultT (
        do  eitherval <- m
            case eitherval of
                Left s -> return $ Left s
                Right a -> let ResultT m' = mf a in m'
        )
instance MonadTrans ResultT where
    lift m = ResultT (Right <$> m)
instance MonadState s m => MonadState s (ResultT m) where
    get = lift get
    put = lift . put
    state = lift . state
instance Monad m => MonadFail (ResultT m) where
    fail s = ResultT (return (Left s))
