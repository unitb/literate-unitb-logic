{-# LANGUAGE TemplateHaskell #-}
module Logic.Proof.POGenerator 
    ( POGen, POGenT -- Logic.Proof.POGenerator.context
    , emit_goal, emit_goal'
    , _context
    , POCtx
    , getContext
    , eval_generator, eval_generatorT
    , with, prefix_label, prefix, named_hyps
    , nameless_hyps, variables, emit_exist_goal
    , Logic.Proof.POGenerator.definitions
    , Logic.Proof.POGenerator.functions 
    , set_syntactic_props
    , setTimeout
    , existential, tracePOG )
where

    -- Modules
import Logic.Expr as E
import Logic.Expr.Existential
import Logic.Proof.Sequent as S

    -- Libraries
import Control.Arrow
import Control.DeepSeq
import Control.Invariant
import Control.Lens hiding (Context)
import Control.Lens.HierarchyTH (mkCons)
import Control.Monad.Identity
import Control.Monad.Reader.Class
import Control.Monad.RWS hiding ((<>))
import Control.Monad.State

import           Data.DList as D
import           Data.List  as L
import           Data.Map as M hiding ( map )
import qualified Data.Map as M
import           Data.Semigroup

import GHC.Generics.Instances

import Text.Printf.TH

import Utilities.Trace

data POParam lbl = POP 
    { _pOParamContext  :: Context
    , tag :: DList lbl
    , _pOParamTimeout  :: Maybe Float
    , _pOParamNameless :: DList Expr
    , _pOParamNamed :: M.Map Label Expr
    , _pOParamSynProp  :: SyntacticProp
    } deriving (Generic)

makeFields ''POParam
mkCons ''POParam
instance NFData lbl => NFData (POParam lbl)

empty_param :: POParam lbl
empty_param = makePOParam

type POGen = POGen' Label
type POGen' lbl = POGenT' lbl Identity
type POGenT = POGenT' Label
newtype POGenT' lbl m a = POGen { runPOGen :: RWST (POParam lbl) (DList (lbl,Sequent)) () m a }
    deriving (Functor,Applicative,Monad,MonadTrans)

type POCtx = POCtx' Label
newtype POCtx' lbl a = POCtx { runPOCxt :: State (POParam lbl) a }
    deriving (Functor,Applicative,Monad)

getContext :: POCtx' lbl Context
getContext = POCtx $ use context

emit_exist_goal :: (HasExpr expr,Monad m,Pre) 
                => [Label] -> [Var] -> [expr] 
                -> POGenT m ()
emit_exist_goal = emit_exist_goal' (as_label . view name)

emit_exist_goal' :: (HasExpr expr,Monad m,Monoid lbl,Pre) 
                 => (Var -> lbl)
                 -> [lbl] -> [Var] -> [expr] 
                 -> POGenT' lbl m ()
emit_exist_goal' mkLbl lbl vars es = with
        (mapM_ prefix_label lbl)
        $ forM_ clauses' $ \(vs,es) -> 
            unless (L.null es) $
                emit_goal'
                    (L.map mkLbl vs) 
                    (zexists vs ztrue $ zall es)
    where
        clauses = partition_expr vars $ L.map getExpr es
        clauses' = M.toList $ (M.fromListWith (<>) clauses :: Map [Var] (NonEmpty Expr))

existential :: (Monad m,Functor m) 
            => [Var] 
            -> POGenT m () 
            -> POGenT m ()
existential = existential' (as_label . view name)

existential' :: (Monad m,Monoid lbl) 
             => (Var -> lbl)
             -> [Var] 
             -> POGenT' lbl m () 
             -> POGenT' lbl m ()
existential' _ [] cmd = cmd
existential' mkLbl vs (POGen cmd) = do
        let g (_, Sequent _ _ ctx _ h0 h1 goal) = do
                    vs <- f ctx
                    return $ zforall vs ztrue $ zall (h0 ++ M.elems h1) `zimplies` goal
            f (Context s vs fs def _) 
                | not $ M.null s = error "existential: cannot add sorts in existentials"
                --      not (M.null fs) 
                --   || not (M.null def) = error "existential: cannot introduce new function symbols in existentials"
                | otherwise = do
                    E.definitions %= merge def
                    E.functions %= merge fs
                    return $ M.elems vs
            -- f xs = [(tag, zexists vs ztrue $ zall $ map snd xs)]
        ss <- POGen 
            $ censor (const D.empty) $ listen 
            $ local (const empty_param) cmd
        let (ss',st) = runState (mapM g $ D.toList $ snd ss) empty_ctx
        with (_context st) 
            $ emit_exist_goal' mkLbl [] vs ss'

emit_goal' :: (Monad m, Monoid lbl, HasExpr expr, Pre) 
           => [lbl] -> expr -> POGenT' lbl m ()
emit_goal' lbl g = emit_goal lbl $ getExpr g

emit_goal :: (Monoid lbl, Monad m, Pre) 
          => [lbl] -> Expr -> POGenT' lbl m ()
emit_goal lbl g = POGen $ do
    tag   <- asks tag 
    param <- ask
    let po = makeSequent
                   (param^.S.context) 
                   (param^.synProp)
                   (D.toList $ param^.nameless)
                   (param^.named)
                   g
               & applyTimeout (param^.timeout)
    unless (g == ztrue) $
        tell $ D.singleton (mconcat $ D.apply tag lbl, po)

setTimeout :: Float -> POCtx' lbl ()
setTimeout = POCtx . assign timeout . Just

set_syntactic_props :: SyntacticProp -> POCtx' lbl ()
set_syntactic_props s = POCtx $ synProp .= s


_context :: Context -> POCtx' lbl ()
_context new_ctx = POCtx $ do
    S.context %= (new_ctx `merge_ctx`)

functions :: M.Map Name Fun -> POCtx' lbl ()
functions new_funs = do
    _context $ Context M.empty M.empty new_funs M.empty M.empty

definitions :: M.Map Name Def -> POCtx' lbl ()
definitions new_defs = POCtx $ do
    S.context.E.definitions .= new_defs

with :: Monad m 
     => POCtx' lbl () 
     -> POGenT' lbl m a 
     -> POGenT' lbl m a
with f cmd = POGen $ local (execState $ runPOCxt f) $ runPOGen cmd

prefix_label :: lbl -> POCtx' lbl ()
prefix_label lbl = POCtx $ do
        tag <- gets tag
        modify $ \p -> p { tag = tag <> D.singleton lbl }

prefix :: String -> POCtx ()
prefix lbl = prefix_label $ label lbl

named_hyps :: HasExpr expr => M.Map Label expr -> POCtx' lbl ()
named_hyps hyps = POCtx $ do
        named %= M.union (M.map getExpr hyps)

nameless_hyps :: HasExpr expr => [expr] -> POCtx' lbl ()
nameless_hyps hyps = POCtx $ do
        nameless <>= D.fromList (L.map getExpr hyps)

variables :: M.Map Name Var -> POCtx' lbl ()
variables vars = POCtx $ do
        S.context.constants %= (vars `merge`)

eval_generator :: (Ord lbl,Show lbl)
               => POGen' lbl () 
               -> M.Map lbl Sequent
eval_generator cmd = runIdentity $ eval_generatorT cmd

tracePOG :: (Monad m,Show lbl) => POGenT' lbl m () -> POGenT' lbl m ()
tracePOG (POGen cmd) = POGen $ do
    xs <- snd <$> listen cmd
    traceM $ unlines $ L.map (show . second (view goal)) (D.toList xs)

eval_generatorT :: (Monad m,Ord lbl,Show lbl) 
                => POGenT' lbl m () 
                -> m (M.Map lbl Sequent)
eval_generatorT cmd = 
            liftM (fromListWithKey combine . D.toList . snd) 
                $ evalRWST (runPOGen cmd) empty_param ()
    where
        combine k _ _ = assertFalse' $ [s|%s\n|] $ show k
