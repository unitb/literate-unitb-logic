{-# LANGUAGE BangPatterns            #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE StandaloneDeriving      #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE TemplateHaskell         #-}
module Logic.Expr.Genericity 
    -- ( TypeSystem2(..)
    -- , typ_fun1, typ_fun2, typ_fun3
    -- , common, check_type, check_type'
    -- , unify, normalize_generics
    -- , ambiguities, suffix_generics
    -- , specialize
    -- , Generic(..)
    -- , instantiate, substitute_types
    -- , substitute_type_vars
    -- , HasTypeVars(..)
    -- , genericsSet
    -- , variablesSet
    -- , types_of
    -- , strip_generics, var_strip_generics
    -- , fun_strip_generics, def_strip_generics
    -- , ctx_strip_generics, type_strip_generics
    -- , OneExprP, TwoExprP, ThreeExprP, FourExprP
    -- , patterns, vars_to_sorts
    -- , gen_to_fol, to_fol_ctx
    -- , match_some, mk_error
    -- , match_all )
where

    -- Modules
import Logic.Expr.Expr 
-- import Logic.Expr.Classes
import Logic.Expr.Context
import Logic.Expr.Label
import Logic.Expr.PrettyPrint
import Logic.Expr.Type
import Logic.Names

    -- Libraries
import Control.Applicative hiding (empty)
import Control.Arrow ((***),(&&&))
import Control.Lens hiding (rewrite,Context)
import Control.Monad
import Control.Monad.List
import Control.Monad.State
import Control.Precondition

import           Data.Bifunctor
import           Data.Either
import           Data.DList as D (toList)
-- import           Data.Hashable
import           Data.List as L hiding ( union )
import           Data.List.Ordered hiding (nub)
import           Data.Map as M 
                    hiding ( map, union, unions, (\\), (!) )
import qualified Data.Map as M
import qualified Data.Maybe as MM
import qualified Data.Set as S 
-- import           Data.Typeable
import           Data.Void

import Prelude as L

import Text.Printf.TH

import Utilities.Functor

suffix_generics :: (IsPolymorphic t)
                => String -> t -> t
suffix_generics xs  = execState $ do
        _GENERIC' %= (('@':xs) `addSuffix`)
        _FromSort._2.traverse %= suffix_generics xs
-- suffix_generics _  v@(VARIABLE _)      = v
-- suffix_generics xs (GENERIC x)         = GENERIC (('@':xs) `addSuffix` x)
-- suffix_generics xs (Gen s ts) = Gen s $ map (suffix_generics xs) ts
--suffix_generics = fmap

-- rewrite_types :: (IsQuantifier q,IsName n)
--               => String
--               -> AbsExpr n Type q -> AbsExpr n Type q
-- rewrite_types xs e = -- typesOf %~ suffix_generics tag
--     case e of
--         Word (Var name t) -> Word (Var name u)
--           where
--             u           = ft t
--         Lit v t         -> Lit v t'
--           where
--             t'          = ft t
--         Cast b e t -> Cast b (rewrite_types xs e) (suffix_generics xs t)
--         Lift e t -> Lift (rewrite_types xs e) (suffix_generics xs t)
--         FunApp f args -> funApp f' new_args
--           where
--             f'          = substitute_types ft f
--             new_args    = map fe args
--         Binder q vs r term t -> rewrite (rewrite_types xs) (Binder q vs r term (ft t))
--         Record e t -> Record (e & traverseRecExpr %~ rewrite_types xs) (ft t)
--     where
--         fe          = rewrite_types xs
--         ft          = suffix_generics xs

type Infer v  = InferT v Maybe
type InferE v = InferT v (Either [String])

newtype InferT v m a = Infer { unInfer :: StateT (TypeVar,Map v TypeVar) m a } 
    deriving (Functor,Applicative,Monad,Alternative,MonadTrans)

mapInfer :: (forall a. m a -> n a) -> InferT v m b -> InferT v n b
mapInfer f (Infer m) = Infer $ mapStateT f m

globalTypeVar :: (Ord v,Monad m)
              => v 
              -> InferT v m (Unif w)
globalTypeVar v = 
        Infer (uses _2 $ M.lookup v) >>= \case
            Nothing -> do
                v' <- newTypeVar'
                Infer $ _2 %= M.insert v v'
                return $ UnifVar v'
            Just v' -> return $ UnifVar v'

newTypeVar :: Monad m => InferT w m (Unif v)
newTypeVar = Infer $ state $ _1 $ liftA2 (,) UnifVar succ

newTypeVar' :: Monad m => InferT w m TypeVar
newTypeVar' = Infer $ state $ _1 $ liftA2 (,) id succ

allocUnifVars :: (Traversable t,Ord v)
             => AbsFun n (t v) 
             -> Infer u (AbsFun n (t (Unif w)))
allocUnifVars = flip evalStateT M.empty . (traverse.traverse) makeUnifVar

makeUnifVar :: Ord v => v -> StateT (Map v (Unif w)) (Infer u) (Unif w)
makeUnifVar v = gets (M.lookup v) 
        >>= maybe (lift newTypeVar >>= \i -> modify (M.insert v i) >> return i) 
                  return

check_args :: (IsQuantifier q,IsName n,IsTypeVar t,Ord v)
           => [AbsExpr n (OpenType t) q] 
           -> AbsFun n (GenericType' v)
           -> Infer u (AbsExpr n (OpenType t) q) 
check_args xs f = check_args' (\f xs _ -> funApp f xs (type_of f)) f xs
check_args' :: (IsQuantifier q,IsName n,IsTypeVar t,Ord v)
            => (AbsFun n (OpenType t) -> [AbsExpr n (OpenType t) q] -> [OpenType t] -> AbsExpr n (OpenType t) q)
            -> AbsFun n (GenericType' v) 
            -> [AbsExpr n (OpenType t) q]
            -> Infer u (AbsExpr n (OpenType t) q) 
check_args' f fun args = do
        (Fun gs name lf ts t wd) <- allocUnifVars fun
        let n       = length ts
        guard (n == length ts)
        rt <- GENERIC <$> newTypeVar
        let 
            -- args    = zipWith _rewrite_types (map show [1..n]) xp
            targs   = L.map type_of args
            -- t0 and t1 are type tuples for the sake of unification
            t0      = Gen IntSort (t:ts) 
            t1      = Gen IntSort (rt:targs)
        uni <- lift $ unify t0 t1
        let 
            fe    = types %~ instantiate uni
            ft    = instantiate uni
            gs2   = map ft gs
            us    = L.map ft ts
            u     = ft t
            args2 = map fe args
            expr = f (Fun gs2 name lf us u wd) args2 us
        return expr
zcast :: (IsQuantifier q,IsName n,IsTypeVar t)
      => OpenType t -> ExprPG n (OpenType t) q
      -> ExprPG n (OpenType t) q
zcast t me = do
        e <- me
        let { err_msg = intercalate "\n"
                        [ [s|expression has type incompatible with its expected type:|]
                        , [s|  expression: %s|]        (pretty e)
                        , [s|  actual type: %s|]       (pretty $ type_of e)
                        , [s|  expected type: %s |]    (pretty t)
                        ] }
        u <- maybe (Left [err_msg]) Right $ 
            unify t $ type_of e
        return $ e & types %~ instantiate u

class TypeSystem t => TypeSystem2 t where
--     check_args :: (IsQuantifier q,IsName n)
--                => [AbsExpr n t q] 
--                -> AbsFun n t 
--                -> Infer (AbsExpr n t q) 
--     check_args xs f = check_args' (\f xs _ -> funApp f xs) f xs
--     check_args' :: (IsQuantifier q,IsName n)
--                 => (AbsFun n t -> [AbsExpr n t q] -> [t] -> AbsExpr n t q)
--                 -> AbsFun n t 
--                 -> [AbsExpr n t q]
--                 -> Infer (AbsExpr n t q) 
--     zcast :: (IsQuantifier q,IsName n)
--           => t -> ExprPG n t q
--           -> ExprPG n t q
--     gUnify :: t -> t -> Maybe (Map InternalName t)

-- instance TypeSystem2 () where
--     check_args' f fun xp = do
--             let ts = fun^.argumentTypes
--             guard (length xp == length ts)
--             return $ f fun xp ts
--     zcast _ = id
--     gUnify () () = Just empty

-- instance TypeSystem2 FOType where
--     check_args' f fun xp = do
--             let ts = fun^.argumentTypes
--             guard (fmap type_of xp == ts)
--             return $ f fun xp ts
--     zcast t me = do
--             e <- me
--             let { err_msg = intercalate "\n"
--                             [ [s|expression has type incompatible with its expected type:|]
--                             , [s|  expression: %s|]        (pretty e)
--                             , [s|  actual type: %s|]       (pretty $ type_of e)
--                             , [s|  expected type: %s |]    (pretty t)
--                             ] }
--             unless (type_of e == t)
--                 $  Left [err_msg]
--             return e
--     gUnify t0 t1 | t0 == t1  = Just empty
--                  | otherwise = Nothing

-- instance (Ord v,Show v,Typeable v,PrettyPrintable v,Hashable v) 
--         => TypeSystem2 (OpenType v) where
--     check_args' f (Fun gs name lf ts t wd) xp = do
--             let n       = length ts
--             guard (n == length ts)
--             let args    = zipWith _rewrite_types (map show [1..n]) xp
--                 targs   = L.map type_of args
--                 rt      = GENERIC (reserved "a" (n+1))
--                 -- t0 and t1 are type tuples for the sake of unification
--                 t0      = Gen IntSort (t:ts) 
--                 t1      = Gen IntSort (rt:targs)
--             uni <- lift $ unify t0 t1
--             let fe x   = _specialize uni . _rewrite_types x
--                 ft x   = _instantiate uni . _suffix_generics x
--                 gs2   = map (ft "1") gs
--                 us    = L.map (ft "1") ts
--                 u     = ft "1" t
--                 args2 = map (fe "2") args
--                 expr = f (Fun gs2 name lf us u wd) args2 us
--             return expr
--     zcast t me = do
--             e <- me
--             let { err_msg = intercalate "\n"
--                             [ [s|expression has type incompatible with its expected type:|]
--                             , [s|  expression: %s|]        (pretty e)
--                             , [s|  actual type: %s|]       (pretty $ type_of e)
--                             , [s|  expected type: %s |]    (pretty t)
--                             ] }
--             u <- maybe (Left [err_msg]) Right $ 
--                 unify t $ type_of e
--             return $ e & types %~ instantiate u
--     gUnify = unify

check_all :: [Either [String] a] -> Either [String] [a]
check_all xs 
    | all isRight xs = Right $ rights xs
    | otherwise      = Left $ concat $ lefts xs

check_type :: (IsQuantifier q,IsName n,IsTypeVar t)
           => AbsFun n (GenericType' t) 
           -> [AbsExpr n (OpenType t) q] 
           -> InferE u (AbsExpr n (OpenType t) q)
check_type = check_type' $ \fun xs _ -> funApp fun xs (type_of fun)

check_type' :: (IsQuantifier q,IsName n,IsTypeVar t)
            => (AbsFun n (OpenType t)
                 -> [AbsExpr n (OpenType t) q] 
                 -> [OpenType t] 
                 -> AbsExpr n (OpenType t) q)
            -> AbsFun n (GenericType' t)
            -> [AbsExpr n (OpenType t) q] 
            -> InferE u (AbsExpr n (OpenType t) q)
check_type' f fun@(Fun _ n _ ts t _) xs = do
        case xs of
            [x]     -> typ_fun1 fun x
            [x,y]   -> typ_fun2 fun x y
            [x,y,z] -> typ_fun3 fun x y z
            _ -> do
                let args = unlines $ map (\(i,x) -> unlines
                                            [ [s|   argument %d:  %s|] i (pretty x)
                                            , [s|   type:          %s|] (pretty $ type_of x) ])
                                (zip [0 :: Int ..] xs)
                    err_msg = unlines
                                [ [s|arguments of '%s' do not match its signature:|] (render n)
                                , [s|   signature: %s -> %s|] (pretty ts) (pretty t)
                                , [s|%s|] args ]
                mapInfer (maybe (Left [err_msg]) Right) $ check_args' f fun xs

type OneExprP n t q   = IsQuantifier q => ExprPG n t q -> ExprPG n t q
type TwoExprP n t q   = IsQuantifier q => ExprPG n t q -> ExprPG n t q -> ExprPG n t q
type ThreeExprP n t q = IsQuantifier q => ExprPG n t q -> ExprPG n t q -> ExprPG n t q -> ExprPG n t q
type FourExprP n t q  = IsQuantifier q => ExprPG n t q -> ExprPG n t q -> ExprPG n t q -> ExprPG n t q -> ExprPG n t q


typ_fun1 :: ( IsName n,IsQuantifier q,IsTypeVar t,PrettyPrintable v,Ord v)
         => AbsFun n (GenericType' v)
         -> AbsExpr n (OpenType t) q
         -> InferE u (AbsExpr n (OpenType t) q)
typ_fun1 f@(Fun _ n _ ts t _) x = do
        let err_msg = unlines
                    [ [s|argument of '%s' do not match its signature:|] (render n)
                    , [s|   signature: %s -> %s|] (pretty ts) (pretty t)
                    , [s|   argument: %s|] (pretty x)
                    , [s|     type %s|] (pretty $ type_of x)
                    ]
        mapInfer (maybe (Left [err_msg]) Right) $ check_args [x] f

typ_fun2 :: ( IsName n,IsQuantifier q,IsTypeVar t,PrettyPrintable v,Ord v)
         => AbsFun n (GenericType' v)  
         -> AbsExpr n (OpenType t) q
         -> AbsExpr n (OpenType t) q
         -> InferE u (AbsExpr n (OpenType t) q)
typ_fun2 f@(Fun _ n _ ts t _) x y     = do
        let err_msg = unlines
                    [ [s|arguments of '%s' do not match its signature:|] (render n)
                    , [s|   signature: %s -> %s|]                        (pretty ts) (pretty t)
                    , [s|   left argument: %s|]                          (pretty x)
                    , [s|     type %s|]                                  (pretty $ type_of x) 
                    , [s|   right argument: %s|]                         (pretty y)
                    , [s|     type %s|]                                  (pretty $ type_of y)
                    ]
        mapInfer (maybe (Left [err_msg]) Right) $ check_args [x,y] f

typ_fun3 :: ( IsName n,IsQuantifier q,IsTypeVar t,PrettyPrintable v,Ord v)
         => AbsFun n (GenericType' v)
         -> AbsExpr n (OpenType t) q
         -> AbsExpr n (OpenType t) q
         -> AbsExpr n (OpenType t) q
         -> InferE u (AbsExpr n (OpenType t) q)
typ_fun3 f@(Fun _ n _ ts t _) x y z  = do
        let err_msg = unlines
                   [ [s|arguments of '%s' do not match its signature:|] (render n) 
                   , [s|   signature: %s -> %s|]                        (pretty ts) (pretty t) 
                   , [s|   first argument: %s|]                         (pretty x)
                   , [s|     type %s|]                                  (pretty $ type_of x) 
                   , [s|   second argument: %s|]                        (pretty y)
                   , [s|     type %s|]                                  (pretty $ type_of y) 
                   , [s|   third argument: %s|]                         (pretty z)
                   , [s|     type %s|]                                  (pretty $ type_of z)
                   ]
        mapInfer (maybe (Left [err_msg]) Right) $ check_args [x,y,z] f

-- instantiate1 :: Int -> OpenType v -> OpenType v -> OpenType v

instantiate' :: (u -> v) 
             -> (TypeVar -> GenericType' v) 
             -> OpenType u 
             -> GenericType' v
instantiate' f g = (>>= typeVar g (pure . f))

instantiate :: Map TypeVar (OpenType v) -> OpenType v -> OpenType v
instantiate s = (>>= typeVar (\v' -> fromMaybe (pure . UnifVar $ v') (v' `M.lookup` s)) (pure . FreeVar))

instantiate1 :: TypeVar -> OpenType v -> OpenType v -> OpenType v
instantiate1 v t = (>>= typeVar (\v' -> if v' == v then t else pure (UnifVar v')) (pure . FreeVar))

unify_aux :: Eq v => [(OpenType v,OpenType v)] -> Maybe (Map TypeVar (OpenType v))
unify_aux ( (GENERIC (UnifVar x), t1) : xs ) 
        | t1 == GENERIC (UnifVar x) = unify_aux xs
        | x `S.member` genericsSet t1 = Nothing
        | otherwise       = do
            -- let s = singleton x t1
            r <- unify_aux $ map (instantiate1 x t1 *** instantiate1 x t1) xs
            -- let s' = singleton x $ instantiate r t1
            return $ M.insert x (instantiate r t1) r
unify_aux ( (t0, t1@(GENERIC (UnifVar _))) : xs ) = unify_aux $ (t1,t0) : xs
unify_aux ( (GENERIC (FreeVar x), GENERIC (FreeVar y)) : xs ) = do
    guard (x == y)
    unify_aux xs
unify_aux ( (Gen x xs, Gen y ys) : zs ) = do
    guard $ x == y &&
        length xs == length ys
    unify_aux $ zip xs ys ++ zs
unify_aux [] = return empty
unify_aux _  = Nothing

unify :: Eq v => OpenType v -> OpenType v -> Maybe (Map TypeVar (OpenType v))
unify t0 t1 = 
    unify_aux [(t0, t1)]

strip_generics :: IsName n 
               => AbsExpr n Type q 
               -> Maybe (AbsExpr InternalName FOType q)
strip_generics = traverseOn3 (return . asInternal) type_strip_generics type_strip_generics pure
--  (Word v)    = do
--     v <- var_strip_generics v
--     return (Word v)
-- strip_generics (Lit m t) = do
--     t  <- type_strip_generics t
--     return (Lit m t)
-- strip_generics (Cast b e t _) = do
--     e <- strip_generics e
--     t <- type_strip_generics t
--     return (Cast b e t)
-- strip_generics (Lift e t) = do
--     e <- strip_generics e
--     t <- type_strip_generics t
--     return (Lift e t)
-- strip_generics (FunApp f xs) = do
--     f  <- fun_strip_generics f
--     xs <- mapM strip_generics xs
--     return (funApp f xs)
-- strip_generics (Binder q vs r t et) = do
--     vs <- mapM var_strip_generics vs
--     r  <- strip_generics r
--     t  <- strip_generics t
--     et' <- type_strip_generics et
--     return (binder q vs r t et')
-- strip_generics (Record e t) = Record 
--         <$> traverseRecExpr strip_generics e
--         <*> type_strip_generics t

type_strip_generics :: GenericType' v -> Maybe FOType
type_strip_generics = traverse $ const Nothing

fun_strip_generics :: IsName n => AbsFun n Type -> Maybe FOFun
fun_strip_generics (Fun ts n lf ps rt wd) = do
    ts <- mapM type_strip_generics ts
    ps <- mapM type_strip_generics ps
    rt <- type_strip_generics rt
    return (Fun ts (asInternal n) lf ps rt wd)

def_strip_generics :: IsName n => AbsDef n Type q -> Maybe (AbsDef InternalName FOType q)
def_strip_generics (Def ts n ps rt val) = do
    ts  <- mapM type_strip_generics ts
    ps  <- mapM var_strip_generics ps
    rt  <- type_strip_generics rt
    val <- strip_generics val
    return (makeDef ts (asInternal n) ps rt val)

var_strip_generics :: IsName n => AbsVar n Type -> Maybe FOVar
var_strip_generics (Var n t) = do
    t <- type_strip_generics t
    return (Var (asInternal n) t)

ctx_strip_generics :: IsName n
                   => (GenContext n GenericType HOQuantifier) 
                   -> Maybe (GenContext InternalName FOType HOQuantifier)
ctx_strip_generics (Context a b c d e) = 
        Context a 
            <$> (mapKeys asInternal <$> traverse var_strip_generics b)
            <*> (mapKeys asInternal <$> traverse fun_strip_generics c)
            <*> (mapKeys asInternal <$> traverse def_strip_generics d)
            <*> (mapKeys asInternal <$> traverse var_strip_generics e)

-- genericsSet    :: HasTypeVars a => a -> S.Set InternalName
genericsSet    :: Foldable f => f (Unif v) -> S.Set TypeVar
genericsSet = S.fromList . genericsList

-- variablesSet   :: HasTypeVars a => a -> S.Set InternalName
-- variablesSet = S.fromList . D.toList . foldMapOf variables pure

-- genericsList :: HasTypeVars a => a -> [InternalName]
genericsList :: Foldable f => f (Unif v) -> [TypeVar]
genericsList = D.toList . foldMap (foldMapOf _UnifVar pure)

types_of    :: (Typed a,Ord (TypeOf a)) => a -> S.Set (TypeOf a)
types_of = S.fromList . D.toList . foldMapOf types pure

-- class (HasTypeVars a,IsPolymorphic (TypeOf a)) --,Generic (TypeOf a) (TypeOf b)) 
--         => Generic a where
--     type WithType t a :: *
--     substitute_types'    :: (TypeOf a -> t) -> a -> WithType t a
--     instantiate' :: Map InternalName t -> a -> WithType t a
--     substitute_type_vars' :: Map InternalName t -> a -> WithType t a

-- substitute_types :: (Generic a,a ~ WithType (TypeOf a) a) => (TypeOf a -> TypeOf a) -> a -> a
-- substitute_types = substitute_types'

-- instantiate :: (Generic a,a ~ WithType (TypeOf a) a) => Map InternalName (TypeOf a) -> a -> a
-- instantiate = instantiate'

-- substitute_type_vars :: (Generic a,a ~ WithType (TypeOf a) a) => Map InternalName (TypeOf a) -> a -> a
-- substitute_type_vars = substitute_type_vars'

-- instance Generic SubType where
--     type WithType t SubType = t
--     substitute_types' f t = rewrite (substitute_types' f) t
--     instantiate' m = _Wrapped %~ instantiate' (unSubType <$> m)
--     substitute_type_vars' m = _Wrapped %~ substitute_type_vars' (unSubType <$> m)

-- instance Generic GenericType where
--     type WithType t GenericType = t
--     substitute_types' f t = rewrite (substitute_types' f) t
--     instantiate' m t = f t
--         where
--             f t0@(GENERIC x) = 
--                 case M.lookup x m of
--                     Just t1  -> t1
--                     Nothing  -> t0
--             f t           = rewrite f t
--     substitute_type_vars' m t = f t
--         where
--             f t0@(VARIABLE x) = 
--                 case M.lookup x m of
--                     Just t1  -> t1
--                     Nothing  -> t0
--             f t           = rewrite f t


-- instance Generic (AbsFun n Type) where
--     type WithType t (AbsFun n Type) = AbsFun n t
--     substitute_types' f (Fun gs n lf ts t wd) = Fun (map f gs) n lf (map f ts) (f t) wd
--     instantiate' m x = substitute_types' (instantiate' m) x
--     substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

-- instance (IsQuantifier q,IsName n) 
--         => Generic (AbsDef n Type q) where
--     type WithType t (AbsDef n Type q) = AbsDef n t q
--     substitute_types' f (Def gs n ts t e) = 
--             makeDef (map f gs) n 
--                     (map (substitute_types' f) ts) 
--                     (f t) 
--                     (substitute_types' f e)
--     instantiate' m x = substitute_types' (instantiate' m) x
--     substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

-- instance (IsName n) => Generic (AbsVar n Type) where
--     type WithType t (AbsVar n Type) = AbsVar n t
--     substitute_types' f (Var x t) = Var x $ f t
--     instantiate' m x = substitute_types' (instantiate' m) x
--     substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

-- instance (IsQuantifier q, TypeSystem t,IsName n) 
--         => Generic (AbsExpr n t q) where
--     type WithType t' (AbsExpr n t q) = AbsExpr n t' q
--     substitute_types' g = rewriteExpr g id (substitute_types' g)
--     instantiate' m x = substitute_types' (instantiate' m) x
--     substitute_type_vars' m x = substitute_types' (substitute_type_vars' m) x

-- ambiguities :: Expr -> [Expr]
-- ambiguities e@(Word (Var _ t))
--         | S.null $ genericsSet t = []
--         | otherwise           = [e]
-- ambiguities e@(Lit _ t)    
--         | S.null $ genericsSet t = []
--         | otherwise           = [e]
-- ambiguities e@(Cast _ e' t)
--         | not $ S.null $ genericsSet t = [e]
--         | otherwise                 = ambiguities e'
-- ambiguities e@(Lift e' t)
--         | not $ S.null $ genericsSet t = [e]
--         | otherwise                 = ambiguities e'
-- ambiguities e@(FunApp f xp)    
--         | not $ L.null children     = children
--         | not $ S.null $ genericsSet f = [e]
--         | otherwise                 = []
--     where
--         children = L.concatMap ambiguities xp
-- ambiguities e@(Binder _ vs r xp t) = x ++ y ++ ambiguities r ++ ambiguities xp
--     where
--         vs' = L.filter (not . S.null . genericsSet . var_type) vs
--         x 
--             | not $ L.null vs' = map Word vs'
--             | otherwise        = []
--         y 
--             | not $ S.null (genericsSet t) = [e]
--             | otherwise                 = []
-- ambiguities r@(Record e t) = x ++ concat (e^.partsOf (traverseRecExpr.to ambiguities))
--     where
--         x   | not $ S.null (genericsSet t) = [r]
--             | otherwise                 = []

-- common :: (TypeSystem2 t,Generic t)
--        => t -> t -> Maybe t
-- common t1 t2 = do
--         m <- gUnify t1 t2 
--         return $ normalize_generics $ instantiate_left m t1

    -- Change the name of generic parameters
    -- to follow alphabetical order: 
    -- a .. z ; aa .. az ; ba .. bz ...
-- normalize_generics :: (Tree t, Generic t) => t -> t
-- normalize_generics expr = evalState (generics std expr) (empty,gen)
--     where
--         std n = do
--                 gets (M.lookup n . fst) >>= \case
--                     Just n' -> return n'
--                     Nothing -> do
--                         n' <- gets $ head . snd
--                         _2 %= tail
--                         _1 %= M.insert n n'
--                         return n'
--         letters = map (:[]) [ 'a' .. 'z' ]
--         gen = map fromString'' gen'
--         gen' = (letters ++ [ x ++ y | x <- gen', y <- letters ])
        -- f (m,names) e = visit f (M.union renaming m, drop n names) e
        --     where
        --         free_gen = nub (genericsList e) L.\\ keys m
        --         renaming = fromList $ zip free_gen names
        --         n        = length free_gen
        -- renaming = fst $ f (empty, map (_ $ GENERIC) gen) expr

-- instantiate_left :: (TypeSystem t,Generic t)
--                  => Map InternalName t -> t -> t
-- instantiate_left m t = instantiate m (suffix_generics "1" t)

-- _instantiate_right :: Map InternalName GenericType -> GenericType -> GenericType
-- _instantiate_right m t = instantiate m (suffix_generics "2" t)

--     -- apply a type substitution to an expression
-- specialize :: (IsQuantifier q,IsName n)
--            => Map InternalName GenericType 
--            -> AbsExpr n Type q -> AbsExpr n Type q
-- specialize = instantiate

-- _specialize_left :: (IsQuantifier q,IsName n)
--                  => Map InternalName GenericType 
--                  -> AbsExpr n Type q -> AbsExpr n Type q
-- _specialize_left m e  = specialize m (rewrite_types "1" e)

-- specialize_right :: (IsQuantifier q,IsName n)
--                  => Map InternalName GenericType 
--                  -> AbsExpr n Type q -> AbsExpr n Type q
-- specialize_right m e = specialize m (rewrite_types "2" e)

    -- instantiation patterns
    -- `patterns ts` is the list of all the types occurring in
    -- ts that has generic parameters and type variables 
    -- and convert all to generic parameters in preparation
    -- for unification
patterns :: (Monad m,IsTypeVar t,IsName n)
         => AbsExpr n (GenericType' t) q 
         -> InferT t m [GenericType' (Unif t)]
patterns e = do
        types <- mapM varToGen $ S.elems $ types_of e
        let pat  = L.filter hg types
        mapM maybe_pattern pat
    where
        hg x = not $ S.null $ genericsSet x
            -- has generics
        -- gen = M.fromSet GENERIC $ S.unions $ L.map variables types
        
        -- gen (VARIABLE s) = (GENERIC s)
        -- gen t = case t^?_VARIABLE' of 
        --             Just s  -> review _GENERIC' s
        --             Nothing -> rewrite gen t

        -- ungen (GENERIC s) = VARIABLE s
        -- ungen t = rewrite ungen t

deUnif :: Unif Void -> InternalName
deUnif = typeVar id absurd

    -- generic to first order
gen_to_fol :: (IsQuantifier q,IsName n,Pre,Monad m)
           => S.Set FOType 
           -> Label 
           -> AbsExpr n Type q 
           -> InferT InternalName m [(Label,AbsExpr InternalName FOType q)]
gen_to_fol types lbl e = do
        e'  <- e & typesOf' varToGen
        let inst m   = e' & typesOf' %~ (instantiate' id (m !))
                          & namesOf  %~ asInternal
        pat <- patterns (first (fmap _) e')
        xs  <- match_all pat (S.elems types)
        return $ map (f &&& inst) xs
    where
        -- inst m = _mk_error ("gen_to_fol", (types_of $ e' m,e))
        --             strip_generics $ e' m
        -- e' m   = _substitute_type_vars (M.map as_generic m) e
        f xs   = composite_label [lbl, label $ concatMap z3_decoration $ M.elems xs]

-- to_fol_ctx :: forall q n. (IsQuantifier q,IsName n)
--            => S.Set FOType 
--            -> GenContext n Type q 
--            -> GenContext InternalName FOType q
-- to_fol_ctx types (Context s vars funs defs dums) = 
--         Context s 
--             vars' funs' defs' dums'
--     where
--         vars' = M.mapKeys asInternal $ M.map fv vars
--         funs' = M.mapKeys asInternal $ decorated_table $ concatMap ff $ M.elems funs
--         defs' = M.mapKeys asInternal $ decorated_table $ concatMap fdf $ M.elems defs
--         dums' = M.mapKeys asInternal $ M.map fdm dums
--         fv    = mk_error () var_strip_generics
--         ff :: AbsFun n Type -> [FOFun]
--         ff fun = map inst xs
--             where
--                 pat    = patterns fun
--                 xs     = match_all pat (S.elems types)
--                 inst :: Pre => Map InternalName FOType -> FOFun
--                 inst m = substitute_type_vars' m fun'

--                 fun' :: AbsFun n Type
--                 fun' = substitute_types genToVar fun
--         fdf def = map inst xs -- M.fromJust . def_strip_generics
--             where 
--                 pat    = patterns def
--                 xs     = L.map (M.map as_generic) 
--                             $ match_all pat (S.elems types)
                
--                 inst :: Map InternalName Type -> AbsDef InternalName FOType q
--                 inst m = mk_error m def_strip_generics $ substitute_type_vars m def'

--                 def' :: AbsDef n Type q               
--                 def' = substitute_types genToVar def
--         fdm = fromJust' . var_strip_generics

liftList :: Monad m => [a] -> ListT m a
liftList = ListT . return

match_all :: (Monad m,Ord w,Eq v) 
          => [GenericType' (Unif v)] 
          -> [FOType] 
          -> InferT w m [Map TypeVar FOType]
match_all pat' types = do
        -- pat' <- mapM varToGen pat
        -- let _ = pat' :: [GenericType' (Unif Void)]
        return $ foldM (\x p -> do
                t  <- types'
                m  <- MM.maybeToList $ unify p t
                ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
                let m'  = M.fromList $ zip (M.keys m) ms
                    -- m'' = M.mapKeys (_ dropSuffix) m'
                guard $ consistent m' x
                return (m' `M.union` x)
            ) M.empty pat'
    where
        types' = map as_generic types

-- match_some :: [Type] -> [FOType] -> [Map InternalName FOType]
-- match_some pat types = nubSort $ do -- map (M.map head) ms -- do
--         ms <- foldM (\x (_,xs) -> do
--                 m <- xs
--                 guard $ consistent m x
--                 return (m `M.union` x)
--             ) M.empty (M.toList ms')
-- --        ms <- forM (toList ms') $ \(k,xs) -> do
-- --            x <- xs
-- --            return (k,x)
-- --        let ms' = fromList ms
--         guard $ M.keysSet ms == vars
--         return ms
--     where
--         pat' = L.map varToGen pat
--         types' = map as_generic types
--         vars = S.unions $ map genericsSet pat'
--         ms' = M.unionsWith (++) ms
-- --        ms :: [Map String [FOType]]
--         ms :: [Map InternalName [Map InternalName FOType]]
--         ms = do
--             p  <- pat'
--             t  <- types'
--             m  <- MM.maybeToList $ unify p t
--             ms <- MM.maybeToList $ mapM type_strip_generics (M.elems m) 
--             let ms' = M.fromList $ zip (map dropSuffix $ M.keys m) ms
--             return $ M.map (const [ms']) ms' 

-- --mk_error :: (Expr -> Maybe FOExpr) -> Expr -> Maybe FOExpr
-- mk_error :: (Show c, Tree a, Pre) 
--          => c -> (a -> Maybe b) -> a -> b
-- mk_error z f x = 
--         case f x of
--             Just y -> y
--             Nothing -> assertFalseMessage $ [s|failed to strip type variables: \n'%s'\n'%s'|] (pretty_print' x) (show z)

consistent :: (Eq b, Ord k) 
           => Map k b -> Map k b -> Bool
consistent x y = x `M.intersection` y == y `M.intersection` x

varToGen :: (Ord u,Monad m)
         => GenericType' u
         -> InferT u m (GenericType' (Unif v))
varToGen = traverse globalTypeVar

-- genToVar :: HasTypeVars a => a -> a
-- genToVar t = case t^?_GENERIC' of
--                 Just n  -> review _VARIABLE' n
--                 Nothing -> rewrite genToVar t

maybe_pattern :: (IsTypeVar t,Monad m)
              => OpenType t -> InferT w m (OpenType t)
maybe_pattern t = do
        a <- pure <$> newTypeVar
        b <- pure <$> newTypeVar
        return $ MM.fromMaybe t $ do
            m <- unify (maybe_type a) t
            return $ instantiate m $ fun_type b a
--     where
--         -- t' = varToGen t
--         -- v2g (VARIABLE x) = GENERIC x
--         -- v2g t = rewrite v2g t

--         gB2 = review _GENERIC' $ reserved "b" 1
--         gA2 = review _GENERIC' $ reserved "a" 1

-- is_maybe :: Type -> Bool
-- is_maybe t = MM.isJust (unify t (maybe_type gA))
--     where
--         gA = GENERIC "a"

type_vars_to_sorts :: Type -> State ([FOType],Map InternalName FOType) FOType
type_vars_to_sorts t = 
        case t of
          GENERIC n -> do
            m <- gets snd
            case n `M.lookup` m of
              Just t -> return t
              Nothing -> do
                t <- gets $ head . fst
                modify $ tail *** M.insert n t
                return t
          Gen s ts  -> make_type s <$> mapM type_vars_to_sorts ts

vars_to_sorts_aux :: AbsExpr n Type q  -> State ([FOType],Map InternalName FOType) (AbsExpr n FOType q)
vars_to_sorts_aux = rewriteExprM type_vars_to_sorts return vars_to_sorts_aux

names :: Pre 
      => String -> [Name]
names n = map (makeName . (n ++) . show) [0 :: Int ..]

vars_to_sorts :: M.Map Name Sort -> AbsExpr n Type q -> AbsExpr n FOType q
vars_to_sorts sorts e = evalState (vars_to_sorts_aux e) (new_sorts, empty)
    where
        new_sorts = map as_type $ names "G" `minus` keys sorts
        as_type n = make_type (Sort n (asInternal n) 0) []
