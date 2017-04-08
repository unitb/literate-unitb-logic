module Z3.Applicative where

import Logic.Expr
import Logic.Proof.Monad

import Z3.Z3

    -- Libraries
import Control.Applicative
import Control.Concurrent.Async
import Control.Lens
import Control.Monad.RWS
import Control.Monad.Trans.Either
import Data.Either.Validation
import Utilities.Syntactic

newtype Z3 a = Z3 (SequentT Expr Concurrently (Validation [Error] a))
    deriving (Functor)

instance Applicative Z3 where
    pure = Z3 . SequentM . RWST . const . \x s -> pure (pure x,s,mempty)
    Z3 (SequentM (RWST f)) <*> Z3 (SequentM (RWST x)) = Z3 $ SequentM $ RWST $ \() s -> liftA2 (comp s) (f () s) (x () s)
        where
            comp s (i,j,k) (i',j',k') = (i <*> i',s,k <> k')

sequent :: SequentM Expr -> Z3 Validity
sequent s = Z3 $ case makeSequent s of
                    SequentM cmd -> SequentM $ mapRWST Concurrently $ do
                            s <- get
                            mapRWST (fmap (toValidation s) . (_Right._1) prove) cmd
                            -- _
    where
        prove = discharge $ label "no label"

toValidation :: Monoid c
             => s 
             -> Either e (a,s,c) 
             -> (Validation e a,s,c)
toValidation s = either (f s) g
    where
        g = _1 %~ Success
        f s es = (Failure es,s,mempty)

withZ3 :: MonadIO m
       => Z3 a 
       -> SequentT Expr (EitherT [Error] m) a
withZ3 (Z3 cmd) = mapSequentT toEitherT cmd 
    where
        toEitherT x = EitherT . liftIO . fmap (validationToEither . _1 id) . runConcurrently $ x

monadic :: SequentT Expr (EitherT [Error] IO) a
        -> Z3 a 
monadic = Z3 . SequentM . mapRWST Concurrently . rewrap . unSequentM
    where
        -- rewrap s = mapRWST $ fmap (toValidation s)
        rewrap m = do
            s <- get
            mapRWST (fmap (toValidation s) . runEitherT) m
