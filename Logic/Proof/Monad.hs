{-# LANGUAGE TemplateHaskell #-}
module Logic.Proof.Monad where

    -- Modules
import Logic.Expr
import Logic.Expr.Parser
import Logic.Expr.Printable
import Logic.Proof.Sequent hiding (makeSequent)
import Logic.Theories
import Logic.WellDefinedness

    -- Libraries
import Control.Lens hiding (Context)
import Control.Monad.Except
import Control.Monad.RWS hiding ((<>))
import Control.Monad.State
import Control.Precondition

import Data.List as L
import Data.Map as M
import Data.Set as S

import GHC.Generics.Instances

import Utilities.Syntactic

type SequentM = SequentM' Expr

type SequentM' expr = SequentT expr (Either [Error])
newtype SequentT expr m a = SequentM 
        { unSequentM :: RWST
              ()
              (SeqDefinitions expr)
              (ParserSetting,[Theory],Map Name Var)
              m a }
    deriving (Functor,Applicative,Monad)

type DispSequent = HOSequent DispExpr

type SequentWithWD = SequentWithWD' Expr
type DispSequentWithWD = SequentWithWD' DispExpr
data SequentWithWD' expr = SequentWithWD
    { _wd :: Sequent
    , _goal :: HOSequent expr }

data SeqDefinitions expr = SeqDefinitions
    { _seqDefinitionsSorts :: [Sort]
    , _vars  :: [Var]
    , _asms  :: Map Label expr
    , _facts :: [expr]
    , _ctxs  :: [Context] }
    deriving Generic

instance Monoid (SeqDefinitions expr) where
    mempty = genericMEmpty
    mappend = genericMAppend
    mconcat = genericMConcat

makeLenses ''SeqDefinitions
makeFields ''SeqDefinitions

runSequent_ :: (HasExpr expr, FromDispExpr expr)
            => SequentM' expr expr
            -> Either [Error] (HOSequent expr)
runSequent_ = fmap _goal . runSequent

runSequent :: (HasExpr expr, FromDispExpr expr)
           => SequentM' expr expr
           -> Either [Error] (SequentWithWD' expr)
runSequent (SequentM cmd) =
    mkSequent <$> evalRWST
                    (unSequentM (mapM_ include preludeTheories) >> cmd)
                    ()
                    (undefined', [], M.empty)

runSequentT :: (HasExpr expr, FromDispExpr expr, Monad m)
            => SequentT expr m expr
            -> m (SequentWithWD' expr)
runSequentT (SequentM cmd) =
    mkSequent <$> evalRWST
                    (unSequentM (mapM_ include preludeTheories) >> cmd)
                    ()
                    (undefined', [], M.empty)

runSequent' :: Pre
            => SequentM Expr -> SequentWithWD
runSequent' = fromRight' . runSequent

runSequent'' :: FromDispExpr expr
             => SequentM' expr a
             -> Either [Error] a
runSequent'' (SequentM cmd) = fst <$> evalRWST
    (unSequentM (mapM_ include preludeTheories) >> cmd)
    ()
    (undefined', [], M.empty)
    where
        unSequentM (SequentM m) = m

mkSequent :: HasExpr expr => (expr, SeqDefinitions expr) -> SequentWithWD' expr
mkSequent (g, (SeqDefinitions s vs asm thms ctx)) = SequentWithWD
    { _goal = empty_sequent
        & goal .~ g
        & named .~ asm
        & nameless .~ thms
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    , _wd = empty_sequent
        & goal .~ well_definedness (zall (getExpr <$> M.elems asm) `zimplies` getExpr g)
        & nameless .~ L.map getExpr thms
        & sorts .~ symbol_table s
        & constants .~ symbol_table vs
        & context %~ merge_ctx (merge_all_ctx ctx)
    }

makeSequent :: (HasExpr expr, FromDispExpr expr)
            => SequentM' expr expr
            -> SequentM' expr (HOSequent expr)
makeSequent (SequentM cmd) = SequentM $ do
        (e,w) <- listen cmd
        s <- get
        lift $ runSequent_ (SequentM $ put s >> tell w >> return e)

mapSequentT :: (forall c c'. m (a,c,c') -> n (b,c,c'))
            -> SequentT expr m a
            -> SequentT expr n b
mapSequentT f (SequentM m) = SequentM $ mapRWST f m

updateSetting :: Monad m
              => SequentT expr m ()
updateSetting = SequentM $ do
    ts <- use _2
    _1 .= theory_setting (empty_theory' "empty") { _extends =
                symbol_table ts }
    ds <- use _3
    _1.decls %= M.union ds

tell' :: (MonadWriter w m)
      => State w k
      -> m ()
tell' cmd = tell $ execState cmd mempty


include :: (FromDispExpr expr,Monad m)
        => Theory -> SequentT expr m ()
include t = do
    SequentM $ do
        --tell ([],[],M.elems $ theory_facts t,[theory_ctx t])
        tell' $ do
            facts .= L.map (fromDispExpr . DispExpr "") (M.elems $ theory_facts t)
            ctxs .= [theory_ctx t]
        _2 %= (t:)
    updateSetting

assume :: Pre
       => String -> ExprP -> SequentM ()
assume s e = assume' s (fromRight' e)

assume' :: (HasExpr expr,Monad m)
        => String -> expr 
        -> SequentT expr m ()
assume' lbl e = do
        collectDeclaration e
        SequentM $ tell' $ asms .= M.singleton (label lbl) e -- tell ([],[],[e'],[])

assumeQ :: (FromDispExpr expr,HasExpr expr,Monad m)
        => String -> (ParserSetting -> DispExpr) 
        -> SequentT expr m ()
assumeQ lbl qexpr = do
        setting <- SequentM $ use _1
        assume' lbl $ fromDispExpr $ qexpr setting

assumeE :: (FromDispExpr expr,HasExpr expr)
        => (String, StringLi) -> SequentM' expr ()
assumeE (lbl, str) = do
        setting <- SequentM $ use _1
        de <- hoistEither $ parse_expr setting str
        let e = fromDispExpr de
        collectDeclaration e
        SequentM $ tell' $ asms .= M.singleton (label lbl) e -- tell ([],[],[e],[])

withContext :: Context -> SequentM' expr ()
withContext = SequentM . tell' . assign ctxs . pure

withDeclarations :: State Context a -> SequentM' expr ()
withDeclarations = withContext . flip execState mempty

collectDeclaration :: (HasExpr expr,Monad m)
                   => expr
                   -> SequentT expr0 m ()
collectDeclaration e = SequentM $ do
        let ts = types_of (getExpr e)^.partsOf (to S.toList.traverse.foldSorts)
        tell' $ sorts .= ts -- tell (ts,[],[],[])

check :: (Pre,Monad m)
      => ExprP -> SequentT expr m Expr
check e = do
        let e' = fromRight' e
        collectDeclaration e'
        return e'

checkQ :: (Pre,Monad m)
       => (ParserSetting -> DispExpr) 
       -> SequentT expr m Expr
checkQ qexpr = do
        setting <- SequentM $ use _1
        check $ Right $ getExpr $ qexpr setting

checkE :: MonadError [Error] m
       => StringLi 
       -> SequentT expr m Expr
checkE str = do
        de <- checkE' str
        let e = getExpr de
        collectDeclaration e
        return e

checkE' :: MonadError [Error] m
        => StringLi 
        -> SequentT expr m DispExpr
checkE' str = do
        setting <- SequentM $ use _1
        hoistEither $ parse_expr setting str

declare :: (Pre,Monad m)
        => String -> Type 
        -> SequentT expr m ExprP
declare n t = do
        declare' $ Var (fromString'' n) t

declare_ :: Pre
         => String -> Type -> SequentM ()
declare_ n t = do
        void $ declare' $ Var (fromString'' n) t

declare' :: Monad m
         => Var 
         -> SequentT expr m ExprP
declare' v = do
        collectDeclaration $ Word v
        SequentM $ do
            tell' $ vars .= [v] -- tell ([],[v],[],[])
            _3 %= insert_symbol v
            _1.decls %= insert_symbol v
        return $ Right $ Word v

declareE :: StringLi -> SequentM' expr ()
declareE str = do
    setting <- SequentM $ use _1
    let ctx = contextOf setting
    vs <- hoistEither $ get_variables'' ctx str (line_info str)
    mapM_ declare' . fmap snd $ vs

parseDeclarations :: [Theory] -> StringLi -> Either [Error] [(Name, Var)]
parseDeclarations ts str = withExpr $ do
    mapM_ include ts
    setting <- SequentM $ use _1
    let ctx = contextOf setting
    vs <- hoistEither $ get_variables'' ctx str (line_info str)
    return vs
    where
        withExpr = runSequent'' :: SequentM a -> Either [Error] a
hoistEither :: MonadError [Error] m
            => Either [Error] a -> SequentT expr m a
hoistEither = SequentM . either throwError return

