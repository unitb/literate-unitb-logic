{-# LANGUAGE TypeFamilies,TemplateHaskell #-}
module Logic.Expr.Expr 
    ( module Logic.Expr.Expr
    , module Logic.Expr.Fun
    , module Logic.Expr.Quantifier
    , module Logic.Expr.Variable
    , HasConstants(..)
    , Loc(..) )
where

    -- Module
import Logic.Expr.Classes as Expr
import Logic.Expr.Fun
import Logic.Expr.PrettyPrint
import Logic.Expr.Scope
import Logic.Expr.Quantifier
import Logic.Expr.Type
import Logic.Expr.Variable
import Logic.Names

    -- Library
import Control.Applicative hiding (Const)
import Control.DeepSeq
import qualified Control.Invariant as I
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens hiding (rewrite,Context,elements
                           ,Const,Context',rewriteM
                           ,Traversable1(..))
import Control.Precondition

import           Data.Data
import           Data.Hashable
import           Data.List as L
import qualified Data.Map as M
import           Data.Serialize
import qualified Data.Set as S

import GHC.Generics hiding (to,from)
import GHC.Generics.Instances

import Language.Haskell.TH.Syntax hiding (Type,Name)

import Test.QuickCheck
import Test.QuickCheck.ZoomEq

import Text.Printf.TH

import Utilities.Functor

type Expr = AbsExpr Name GenericType HOQuantifier

type FOExpr = AbsExpr InternalName FOType FOQuantifier

type AbsExpr n t q = GenExpr n t t q

type RawExpr = AbsExpr InternalName Type HOQuantifier

type Expr' = AbsExpr InternalName Type FOQuantifier

type ExprSub = AbsExpr Name SubType HOQuantifier

type UntypedExpr = UntypedExpr' GenericType

type UntypedExpr' t = GenExpr Name () t HOQuantifier

data CastType = Parse | CodeGen | WDGuarded
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Enum,Bounded)

data GenExpr n t a q = 
        Word !(AbsVar n t) 
        | Record !(RecordExpr (GenExpr n t a q)) t
        | Lit !Value !t
        | FunApp !(AbsFun n a) ![GenExpr n t a q]
        | Binder !q ![AbsVar n t] !(GenExpr n t a q) !(GenExpr n t a q) !t
        | Cast !CastType !(GenExpr n t a q) !a
        | Lift !(GenExpr n t a q) !a
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Functor,Foldable,Traversable)
type RecFields expr = M.Map Field expr

data RecordExpr expr =
        RecLit !(RecFields expr)
        | RecUpdate !expr !(RecFields expr)
        | RecSet !(RecFields expr)
        | FieldLookup !expr !Field
    deriving (Eq,Ord,Typeable,Data,Generic,Show,Functor,Foldable,Traversable)

data Value = RealVal !Double | IntVal !Int
    deriving (Eq,Ord,Generic,Typeable,Data,Show)

instance PrettyPrintable Value where
    pretty (RealVal v) = show v
    pretty (IntVal v)  = show v

instance ZoomEq Value where
    (.==) = (I.===)

instance ZoomEq CastType where
instance (ZoomEq n,ZoomEq t,ZoomEq a,ZoomEq q) => ZoomEq (GenExpr n t a q) where
instance Arbitrary CastType where
    arbitrary = elements $ enumFromTo minBound maxBound
instance (Arbitrary t,Arbitrary n,Arbitrary a,Arbitrary q,TypeSystem t,IsQuantifier q) 
        => Arbitrary (GenExpr n t a q) where
    arbitrary = do
        inductive $ \arb -> 
            [ Word   <$> arbitrary' 
            , Lit    <$> arbitrary' <*> arbitrary'
            , funApp <$> arbitrary' <*> listOf' arb
            , binder <$> arbitrary' <*> arbitrary' <*> arb <*> arb <*> arbitrary'
            , Cast   <$> arbitrary' <*> arb <*> arbitrary'
            , Lift   <$> arb <*> arbitrary'
            ]
    shrink = genericShrink

mkRecord :: (TypeSystem t,TypeSystem a,TypeAnnotationPair t a) 
         => RecordExpr (GenExpr n t a q) -> Maybe (GenExpr n t a q)
mkRecord (RecLit m) = Just $ Record (RecLit m) (record_type $ type_of <$> m)
mkRecord r@(RecUpdate e m) = Record r . record_type . (M.map type_of m `M.union`) <$> (type_of e^?fieldTypes) 
mkRecord r@(RecSet m) = Just $ Record r $ record_type $ set_type . type_of <$> m
mkRecord r@(FieldLookup e fields) = do
      t <- type_of e^?fieldTypes
      Record r <$> M.lookup fields t

arbitraryRecord :: (RecordExpr expr -> expr)
                -> Gen expr
                -> Gen (RecordExpr expr)
arbitraryRecord mkExpr arb = oneof 
      [ rec
      -- , RecUpdate <$> arb <*> arbitraryFields arb
      , liftA2 FieldLookup (mkExpr <$> rec) arbitrary ]
    where
      recLit = RecLit <$> arbitraryFields arb
      recUpd e = RecUpdate e <$> arbitraryFields arb
      updateOnce = StateT $ fmap ((),) . recUpd . mkExpr
      rec = do
        n <- choose (0,2)
        execStateT (replicateM n updateOnce) =<< recLit

arbitraryFields :: (Arbitrary k,Ord k)
                => Gen a -> Gen (M.Map k a)
arbitraryFields arb = M.fromList <$> fields
    where
      fields = do
          n <- choose (0,3) 
          replicateM n 
              $ liftM2 (,) arbitrary arb

instance (ZoomEq expr) 
        => ZoomEq (RecordExpr expr) where

instance (Arbitrary t,Arbitrary n,Arbitrary a,Arbitrary q,TypeSystem t,IsQuantifier q) 
        => Arbitrary (RecordExpr (GenExpr n t a q)) where
    arbitrary = undefined' -- arbitraryRecord mkRecord arbitrary
    shrink = genericShrink

instance Functor1 (GenExpr a b) where
instance Functor2 (GenExpr a) where
instance Functor3 GenExpr where
instance Foldable1 (GenExpr a b) where
instance Foldable2 (GenExpr a) where
instance Foldable3 GenExpr where

instance Hashable Value
instance Hashable CastType
instance (Hashable n,Hashable t,Hashable a,Hashable q) 
        => Hashable (GenExpr n t a q) where

instance (Hashable expr) => Hashable (RecordExpr expr) where

binder :: q -> [AbsVar n t]
       -> GenExpr n t a q
       -> GenExpr n t a q
       -> t
       -> GenExpr n t a q
binder q = Binder q . evalList

funApp :: AbsFun n a -> [GenExpr n t a q] -> GenExpr n t a q
funApp fun = FunApp fun . evalList

{-# INLINE traverseRecExpr #-}
traverseRecExpr :: Traversal (RecordExpr expr) (RecordExpr expr')
                             expr expr'
traverseRecExpr f (RecLit m) = RecLit <$> traverse f m
traverseRecExpr f (RecSet m) = RecSet <$> traverse f m
traverseRecExpr f (RecUpdate x m) = 
      liftA2 RecUpdate (f x) (traverse f m)
traverseRecExpr f (FieldLookup x field) = liftA2 FieldLookup (f x) (pure field)

instance Traversable1 (GenExpr a b) where
instance Traversable2 (GenExpr a) where

instance Traversable3 GenExpr where
    traverseOn3 f g _ _ (Word v) = Word <$> traverseOn1 f g v
    traverseOn3 _ g _ _ (Lit v t) = Lit v <$> g t
    traverseOn3 f g h p (Cast b e t)   = Cast b <$> traverseOn3 f g h p e <*> h t
    traverseOn3 f g h p (Lift e t)     = Lift <$> traverseOn3 f g h p e <*> h t
    traverseOn3 f g h p (FunApp fun e) = funApp <$> traverseOn1 f h fun <*> traverse (traverseOn3 f g h p) e
    traverseOn3 f g h p (Binder a b c d e) = binder
                                              <$> p a
                                              <*> traverse (traverseOn1 f g) b
                                              <*> traverseOn3 f g h p c
                                              <*> traverseOn3 f g h p d
                                              <*> g e
    traverseOn3 f g h p (Record x t) = Record 
          <$> traverseRecExpr (traverseOn3 f g h p) x
          <*> g t

instance (IsName n) => Translatable 
        (GenExpr n t a q) 
        (GenExpr InternalName t a q) where
    translate = fmap3 asInternal

make_unique :: (IsGenExpr expr, Name ~ NameT expr)
            => String               -- suffix to be added to the name of variables
            -> M.Map Name var       -- set of variables that must renamed
            -> expr                 -- expression to rewrite
            -> expr
make_unique suf vs = freeVarsOf.namesOf %~ newName
    where
        newName vn | vn `M.member` vs = setSuffix suf vn
                   | otherwise        = vn


expSize :: GenExpr n t a q -> Int
expSize (Word _) = 0
expSize (Lit _ _)   = 0
expSize (Record (RecLit m) _) = 1 + sum (M.map expSize m)
expSize (Record (RecSet m) _) = 1 + sum (M.map expSize m)
expSize (Record (RecUpdate e m) _) = 1 + expSize e + sum (M.map expSize m)
expSize (Record (FieldLookup e _) _) = 1 + expSize e
expSize (FunApp _ xs) = 1 + sum (fmap expSize xs)
expSize (Binder _ _ r t _) = 1 + expSize r + expSize t
expSize (Cast _ e _)  = 1 + expSize e
expSize (Lift e _)    = 1 + expSize e

instance Arbitrary Value where
    arbitrary = genericArbitrary
    shrink = genericShrink

type P = Either [String]

type RawExprP = Either [String] RawExpr 

type ExprP = Either [String] Expr 

type ExprP' = Either [String] Expr'

type ExprPG n t q = Either [String] (AbsExpr n t q)

type GenExprPG n t a q = Either [String] (GenExpr n t a q)

type ExprPC e = Either [String] e

class ( TypeSystem (TypeT expr)
      , TypeSystem (AnnotT expr)
      , IsName (NameT expr)
      , TypeAnnotationPair (TypeT expr) (AnnotT expr)
      , IsQuantifier (QuantT expr)
      , Typeable expr
      , VarT expr ~ AbsVar (NameT expr) (TypeT expr)
      , expr ~ GenExpr (NameT expr) (TypeT expr) (AnnotT expr) (QuantT expr)) 
    => IsGenExpr expr where
    type NameT expr :: *
    type TypeT expr :: *
    type AnnotT expr :: *
    type QuantT expr :: *
    type VarT expr :: *
    type FunT expr :: *
    type SetTypeT t expr :: *
    type SetAnnotT t expr :: *
    type SetQuantT t expr :: *

class (IsGenExpr (ExprT expr),Typeable expr) => HasGenExpr expr where
    type ExprT expr :: *
    asExpr :: expr -> ExprT expr
    ztrue :: expr
    zfalse :: expr
    zword :: VarT (ExprT expr) -> expr

instance ( IsName n
         , TypeSystem a
         , TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q) 
         => IsGenExpr (GenExpr n t a q) where
    type VarT (GenExpr n t a q)   = AbsVar n t
    type FunT (GenExpr n t a q)   = AbsFun n t
    type NameT (GenExpr n t a q)  = n
    type TypeT (GenExpr n t a q)  = t
    type AnnotT (GenExpr n t a q) = a
    type QuantT (GenExpr n t a q) = q
    type SetTypeT arg (GenExpr n t a q)  = GenExpr n arg a q
    type SetAnnotT arg (GenExpr n t a q) = GenExpr n t arg q
    type SetQuantT arg (GenExpr n t a q) = GenExpr n t a arg

true_fun :: (IsName n, TypeSystem t) => AbsFun n t
true_fun = mkConstant "true" bool

false_fun :: (IsName n, TypeSystem t) => AbsFun n t
false_fun = mkConstant "false" bool

instance ( IsName n
         , TypeSystem a
         , TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q)
        => HasGenExpr (GenExpr n t a q) where
    type ExprT (GenExpr n t a q)  = GenExpr n t a q
    asExpr = id
    ztrue  = funApp true_fun []
    zfalse = funApp false_fun []
    zword  = Word

class ( IsGenExpr expr, AnnotT expr ~ TypeT expr )
    => IsAbsExpr expr where

instance (IsName n,TypeSystem t,IsQuantifier q) 
        => IsAbsExpr (AbsExpr n t q) where

var_type :: AbsVar n t -> t
var_type (Var _ t) = t


instance ( TypeSystem t,TypeSystem a
         , TypeAnnotationPair t a ) 
        => Typed (GenExpr n t a q) where
    type TypeOf (GenExpr n t a q) = t
    type_of e = type_of $ aux e
        where
            aux (Word (Var _ t))       = t
            aux (Lit _ t)              = t
            aux (Cast _ _ t)           = strippedType t
            aux (Lift _ t)             = strippedType t
            aux (Record _ t)           = t
            aux (FunApp (Fun _ _ _ _ t _) _) = strippedType t
            aux (Binder _ _ _ _ t)   = t
    types = typesOf

typeOfRecord :: ( TypeSystem a,TypeSystem t
                , TypeAnnotationPair t a
                , Pre)
             => RecordExpr (GenExpr n t a q) -> t
typeOfRecord (RecLit m) = recordTypeOfFields m
typeOfRecord (RecSet m) = record_type $ type_of <$> m
typeOfRecord (RecUpdate x m) = recordTypeOfFields $ 
              M.map type_of m `M.union` fromJust' (type_of x^?fieldTypes) 
typeOfRecord (FieldLookup x field) = fromJust' (type_of x^?fieldTypes.ix field)

fieldTypes :: TypeSystem t => Prism' t (M.Map Field t)
fieldTypes =  _FromSort.swapped.below _RecordSort
            . iso (\(ts,m) -> m & unsafePartsOf traverse .~ ts) 
                  (\m -> (M.elems m,() <$ m))

recordTypeOfFields :: (Typed e, t ~ TypeOf e,TypeSystem t) => M.Map Field e -> t
recordTypeOfFields m = make_type (RecordSort $ () <$ m) $ type_of <$> M.elems m

ztuple_type :: TypeSystem t => [t] -> t
ztuple_type []          = null_type
ztuple_type [x]         = x
ztuple_type [x0,x1]     = pair_type x0 $ pair_type x1 null_type
ztuple_type (x0:x1:xs)  = pair_type x0 $ ztuple_type (x1:xs)

ztuple :: (IsName n,TypeSystem t,IsQuantifier q) => [AbsExpr n t q] -> AbsExpr n t q
ztuple []           = unit
ztuple [x]          = x
ztuple [x0,x1]      = pair x0 $ pair x1 unit    -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]
ztuple (x0:x1:xs)   = pair x0 $ ztuple (x1:xs)  -- FunApp (Fun [tx, txs] "pair" [tx, txs] pair_type) [x,tail]

unit :: (TypeSystem t,IsName n) => AbsExpr n t q
unit = funApp (mkConstant "null" null_type) []

pair :: (IsName n,TypeSystem t,IsQuantifier q) => AbsExpr n t q -> AbsExpr n t q -> AbsExpr n t q
pair x y = funApp fun [x,y]
    where
        fun = mk_fun [] (fromString'' "pair") [t0,t1] $ pair_type t0 t1
        t0 = type_of x
        t1 = type_of y

freeVarsOf :: IsGenExpr expr
           => Traversal' expr (VarT expr)
freeVarsOf f = freeVarsOf'' (const f) M.empty

freeVarsOf'' :: (IsGenExpr expr, n ~ NameT expr,Applicative f) 
             => (M.Map n (VarT expr) -> VarT expr -> f (VarT expr))
             -> M.Map n (VarT expr)
             -> expr -> f expr
freeVarsOf'' f vs (Word v) | (v^.name) `M.member` vs = pure (Word v)
                           | otherwise       = Word <$> f vs v
freeVarsOf'' f vs e@(Binder _ us _ _ _) = 
        rewriteM (freeVarsOf'' f $ M.union vs $ symbol_table us) e
freeVarsOf'' f vs e = rewriteM (freeVarsOf'' f vs) e

varsOf :: IsGenExpr expr
       => Traversal' expr (VarT expr)
varsOf f (Word v) = Word <$> f v
varsOf f t = rewriteM (varsOf f) t

subexprs :: IsGenExpr expr
         => Traversal' expr expr
subexprs = rewriteExprM' pure pure pure

typesOf :: Traversal (GenExpr n t0 a q) (GenExpr n t1 a q)
                     t0 t1
typesOf = traverse2

typesOf' :: Traversal (AbsExpr n t0 q) (AbsExpr n t1 q)
                      t0 t1
typesOf' f = rewriteExprM f pure (typesOf' f)

instance HasNames (GenExpr n t a q) n where
    type SetNameT n' (GenExpr n t a q) = GenExpr n' t a q
    namesOf = traverse3

instance (TypeSystem t) => Plated (AbsDef n t q) where
    plate _ = pure
instance (IsName n,TypeSystem t, IsQuantifier q) => Tree (AbsDef n t q) where
    as_tree' d@(Def _ _ argT rT e) = Expr.List <$> sequenceA
            [ Str  <$> render_decorated d
            , Expr.List <$> mapM as_tree' argT 
            , as_tree' rT 
            , as_tree' e ]

target :: AbsDef n t q -> AbsExpr n t q
target (Def _ _ _ _ e) = e

type FODef = AbsDef InternalName FOType HOQuantifier

type Def = AbsDef Name GenericType HOQuantifier

type Def' = AbsDef InternalName GenericType FOQuantifier

data AbsDef n t q = Def ![t] !n ![AbsVar n t] !t !(AbsExpr n t q)
    deriving (Eq,Ord,Generic,Typeable,Data,Functor,Foldable,Traversable,Show)

makeDef :: [t] -> n 
        -> [AbsVar n t] -> t 
        -> AbsExpr n t q
        -> AbsDef n t q
makeDef ps n args t e = Def (evalList ps) n (evalList args) t e

instance HasScope Def where
    scopeCorrect' (Def _tp _n args _t e) = withVars args $ scopeCorrect' e

instance Functor1 (AbsDef n) where
instance Functor2 AbsDef where

instance Foldable1 (AbsDef n) where
instance Foldable2 AbsDef where

instance Traversable1 (AbsDef n) where
instance Traversable2 AbsDef where
    traverseOn2 f g h (Def a b c d e) = 
        makeDef 
          <$> traverse g a 
          <*> f b
          <*> traverse (traverseOn1 f g) c
          <*> g d 
          <*> traverseOn3 f g g h e

instance HasNames (AbsDef n t q) n where
    type SetNameT m (AbsDef n t q) = AbsDef m t q
    namesOf = traverse2

z3Def :: Pre 
      => [Type] 
      -> String
      -> [Var] -> Type -> Expr
      -> Def
z3Def ts n = makeDef ts (z3Name n)

lookupFields :: ( TypeSystem t,TypeSystem a
                , Pre
                , TypeAnnotationPair t a) 
             => GenExpr n t a q -> M.Map Field (GenExpr n t a q)
lookupFields e = fromJust' $ type_of e^?fieldTypes >>= fieldLookupMap
    where
      fieldLookupMap = itraverse $ \f _ -> mkRecord $ FieldLookup e f

instance ( ZoomEq t
         , ZoomEq n
         , ZoomEq q) 
        => ZoomEq (AbsDef n t q) where

instance ( TypeSystem t
         , IsQuantifier q
         , Arbitrary t
         , Arbitrary n
         , Arbitrary q) 
        => Arbitrary (AbsDef n t q) where
    arbitrary = genericArbitrary
    shrink = genericShrink

instance (TypeSystem a, TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q, IsName n)
        => Tree (GenExpr n t a q) where
    as_tree' (Cast CodeGen e t)   = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ Expr.List [Str "as", e', t']
    as_tree' (Cast Parse e _)   = as_tree' e
    as_tree' (Cast WDGuarded e _)   = do
        Expr.List <$> sequence [return $ Str "fromJust",as_tree' e]
    as_tree' (Lift e t) = do
        t' <- as_tree' t
        e' <- as_tree' e
        return $ Expr.List [ Expr.List [ Str "as", Str "const", t']
                             , e']
    as_tree' (Record (RecLit m) _)  = 
        Expr.List <$> liftA2 (:) 
            (pure $ Str $ render (recordName m)) 
            (traverse as_tree' $ M.elems m)
    as_tree' (Record (RecSet m) _)  = 
        Expr.List <$> liftA2 (:) 
            (pure $ Str $ render (recordName m)) 
            (traverse as_tree' $ M.elems m)
    as_tree' (Record (RecUpdate x m') _)  = 
            Expr.List <$> liftA2 (:) 
                (pure $ Str $ render (recordName m)) 
                (traverse as_tree' $ M.elems m)
        where
          m = m' `M.union` lookupFields x
    as_tree' (Record (FieldLookup x field) _) =
        Expr.List <$> sequenceA [pure $ Str $ accessor field, as_tree' x]
    as_tree' (Word (Var xs _))    = return $ Str $ render xs
    as_tree' (Lit xs _)         = return $ Str $ pretty xs
    as_tree' (FunApp f@(Fun _ _ _ _ t _) [])
            | isLifted f = Expr.List <$> sequence   
                               [ Expr.List 
                                 <$> (map Str ["_","map"] ++) 
                                 <$> mapM as_tree' [t]
                               , Str <$> render_decorated f
                               ]
            | otherwise  = Str <$> render_decorated f
    as_tree' (FunApp f ts)  = do
        ts' <- mapM as_tree' ts
        f   <- if isLifted f 
            then (Expr.List . map Str) 
                            <$> (["_","map"] ++) 
                            <$> mapM render_decorated [f]
            else Str <$> render_decorated f
        return $ Expr.List (f : ts')
    as_tree' (Binder q xs r xp _)  = do
        xs' <- mapM as_tree' xs
        r'  <- as_tree' r
        xp' <- as_tree' xp
        return $ Expr.List [ Str $ pretty q
                      , Expr.List xs'
                      , Expr.List 
                          [ merge_range q
                          , r'
                          , xp' ] ]
    -- {-# INLINE rewriteM #-}

instance (TypeSystem a, TypeSystem t)
        => Plated (GenExpr n t a q) where
    plate _ x@(Word _)           = pure x
    plate _ x@(Lit _ _)        = pure x
    plate f (Record e t)       = Record <$> traverseRecExpr f e <*> pure t
    plate f (Lift e t)    = Lift <$> f e <*> pure t
    plate f (Cast b e t)  = Cast b <$> f e <*> pure t
    plate f (FunApp g xs) = funApp g <$> traverse f xs
    plate f (Binder q xs r x t)  = binder q xs <$> f r <*> f x <*> pure t

rewriteExpr :: (t0 -> t1)
            -> (q0 -> q1)
            -> (AbsExpr n t0 q0 -> AbsExpr n t1 q1)
            -> AbsExpr n t0 q0 -> AbsExpr n t1 q1
rewriteExpr fT fQ fE = runIdentity . rewriteExprM 
        (return . fT) (return . fQ) (return . fE)

rewriteExprM' :: (Applicative m)
              => (t0 -> m t1)
              -> (a0 -> m a1)
              -> (q0 -> m q1)
              -> (GenExpr n t0 a0 q0 -> m (GenExpr n t1 a1 q1))
              -> GenExpr n t0 a0 q0 -> m (GenExpr n t1 a1 q1)
rewriteExprM' fT fA fQ fE e = 
        case e of
            Word v -> Word <$> fvar v
            Lit v t -> Lit v <$> fT t
            FunApp f args -> 
                funApp <$> ffun f
                       <*> traverse fE args
            Binder q vs re te t ->
                binder <$> fQ q 
                       <*> traverse fvar vs 
                       <*> fE re
                       <*> fE te
                       <*> fT t
            Cast b e t -> Cast b <$> fE e <*> fA t
            Lift e t -> Lift <$> fE e <*> fA t
            Record e t  -> Record <$> traverseRecExpr fE e <*> fT t
    where
        ffun (Fun ts n lf targs rt wd) = 
                Fun <$> traverse fA ts 
                    <*> pure n <*> pure lf
                    <*> traverse fA targs 
                    <*> fA rt
                    <*> pure wd
        fvar (Var n t) = Var n <$> fT t

rewriteExprM :: (Applicative m)
             => (t0 -> m t1)
             -> (q0 -> m q1)
             -> (AbsExpr n t0 q0 -> m (AbsExpr n t1 q1))
             -> AbsExpr n t0 q0 -> m (AbsExpr n t1 q1)
rewriteExprM fT = rewriteExprM' fT fT

instance ( TypeSystem a,TypeSystem t
         , TypeAnnotationPair t a
         , IsQuantifier q,IsName n) 
        => PrettyPrintable (GenExpr n t a q) where
    pretty e = pretty $ runReader (as_tree' e) UserOutput

instance (TypeSystem t, IsQuantifier q, IsName n) => PrettyPrintable (AbsDef n t q) where
    pretty (Def xs n ps t e) = render n ++ showL xs ++  ": " 
        ++ args ++ pretty (as_tree t)
        ++ "  =  " ++ pretty (as_tree e)
        where
            showL [] = ""
            showL xs = pretty xs ++ " "
            args
                | L.null ps = ""
                | otherwise = intercalate " x " (map (pretty . as_tree) ps) ++ " -> "

instance TypeSystem t => Typed (AbsDef n t q) where
    type TypeOf (AbsDef n t q) = t
    type_of (Def _ _ _ t _) = t
    types f (Def ps n ts t e) = Def ps n <$> (traverse.types) f ts 
                                         <*> types f t 
                                         <*> types f e

dataConstrs :: Sort -> M.Map Name Fun
dataConstrs (Sort _ _ _) = M.empty
dataConstrs (DefSort _ _ _ _) = M.empty
dataConstrs BoolSort   = M.empty
dataConstrs IntSort    = M.empty
dataConstrs RealSort   = M.empty
dataConstrs (RecordSort _) = M.empty
dataConstrs s@(Datatype ps _ cs) = M.fromList $ L.map mkFun cs
    where
      tps = L.map (GENERIC . asInternal) ps
      mkFun (n,args) = (n, 
          mk_fun 
            tps 
            n (L.map snd args) 
            (make_type s tps))

defAsVar :: AbsDef n t q -> Maybe (AbsVar n t)
defAsVar (Def [] n [] t _) = Just $ Var n t
defAsVar _ = Nothing

instance HasScope Expr where
    scopeCorrect' e = do
        let free = used_var' e
        areVisible [vars,constants] free e

merge :: (Ord k, Eq a, Show k, Show a)
          => M.Map k a -> M.Map k a -> M.Map k a
merge m0 m1 = M.unionWithKey f m0 m1
    where
        f k x y
            | x == y    = x
            | otherwise = error $ [s|conflicting declaration for key %s: %s %s|] 
                            (show k) (show x) (show y)

merge_all :: (Ord k, Eq a, Show k, Show a)
          => [M.Map k a] -> M.Map k a
merge_all ms = foldl' (M.unionWithKey f) M.empty ms
    where
        f k x y
            | x == y    = x
            | otherwise = error $ [s|conflicting declaration for key %s: %s %s|]
                            (show k) (show x) (show y)

substitute :: (TypeSystem t, IsQuantifier q, IsName n)
           => M.Map n (AbsExpr n t q) 
           -> (AbsExpr n t q) -> (AbsExpr n t q)
substitute m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (v^.name) m
        f e@(Binder _ vs _ _ _) = rewrite (substitute $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

substitute' :: (TypeSystem t, TypeSystem a, IsQuantifier q, IsName n, TypeAnnotationPair t a)
           => M.Map n (GenExpr n t a q)
           -> (GenExpr n t a q) -> (GenExpr n t a q)
substitute' m e = f e
    where
        f e@(Word v) = maybe e id $ M.lookup (v^.name) m
        f e@(Binder _ vs _ _ _) = rewrite (substitute' $ subst vs) e
        f e = rewrite f e
        subst vs = m M.\\ symbol_table vs

used_var :: ( TypeSystem a,TypeSystem t
            , TypeAnnotationPair t a
            , IsQuantifier q, IsName n) 
         => GenExpr n t a q -> S.Set (AbsVar n t)
used_var (Word v) = S.singleton v
used_var (Binder _ vs r expr _) = (used_var expr `S.union` used_var r) `S.difference` S.fromList vs
used_var expr = visit (\x y -> S.union x (used_var y)) S.empty expr

used_var' :: HasGenExpr expr => expr -> M.Map (NameT (ExprT expr)) (VarT (ExprT expr))
used_var' = symbol_table . S.toList . used_var . asExpr

used_fun :: (TypeSystem t, IsQuantifier q, IsName n) 
         => AbsExpr n t q -> S.Set (AbsFun n t)
used_fun e = visit f s e
    where
        f x y = S.union x (used_fun y)
        s = case e of
                FunApp f _ -> S.singleton f
                _          -> S.empty

free_vars' :: HasExpr expr
           => M.Map Name Var -> expr -> M.Map Name Var
free_vars' ds e = vs `M.intersection` ds
    where
        vs = used_var' (getExpr e)

instance HasName (AbsDef n t q) n where
    name = to $ \(Def _ x _ _ _) -> x

instance (TypeSystem t,IsName n,Typeable q) => Named (AbsDef n t q) where
    type NameOf (AbsDef n t q) = n
    decorated_name' (Def ts x _ _ _) = do
            ts' <- mapM z3_decoration' ts
            let suf = concat ts'
            onInternalName (addSuffix suf) 
                $ adaptName x

used_types :: (TypeSystem t,IsQuantifier q,IsName n) 
           => AbsExpr n t q -> S.Set t
used_types e = visit (flip $ S.union . used_types) (
        case e of
            Binder _ vs e0 e1 t -> S.fromList $ t : type_of e0 : type_of e1 : L.map f vs
            _ -> S.singleton $ type_of e
            ) e
    where
        f (Var _ t) = t

rename :: (TypeSystem t, IsQuantifier q, IsName n) 
       => n -> n
       -> AbsExpr n t q -> AbsExpr n t q
rename x y e@(Word (Var vn t))
        | vn == x   = Word (Var y t)
        | otherwise = e
rename x y e@(Binder q vs r xp t)
        | x `elem` L.map (view name) vs  = e
        | otherwise             = Binder q vs (rename x y r) (rename x y xp) t
rename x y e = rewrite (rename x y) e 

primeOnly :: M.Map Name var -> Expr -> Expr
primeOnly vs = freeVarsOf %~ pr
    where
        pr v | (v^.name) `M.member` vs = prime v
             | otherwise               = v

defExpr :: Lens' (AbsDef n t q) (AbsExpr n t q) 
defExpr f (Def ps n args rt e) = makeDef ps n args rt <$> f e

funOf :: (TypeSystem t) 
      => AbsDef n t q -> AbsFun n t
funOf (Def ps n args rt _e) = Fun ps n Unlifted (map type_of args) rt InfiniteWD

class (IsGenExpr e
        , Show e
        , PrettyPrintable e, Eq e
        , NameT e ~ Name
        , TypeT e ~ Type
        , AnnotT e ~ Type
        , QuantT e ~ HOQuantifier )
        => IsExpr e where

class (IsGenExpr e
        , Show e
        , PrettyPrintable e, Eq e
        , NameT e ~ InternalName
        , TypeT e ~ Type
        , AnnotT e ~ Type
        , QuantT e ~ HOQuantifier )
        => IsRawExpr e where

getExpr :: HasExpr e => e 
        -> AbsExpr (NameT (ExprT e)) Type HOQuantifier
getExpr = asExpr

class (HasGenExpr e,Show e,PrettyPrintable e,Eq e,IsExpr (ExprT e),HasScope e) => HasExpr e where
class (HasGenExpr e,IsRawExpr (ExprT e),HasScope e) => HasRawExpr e where

instance Lift CastType where
    lift = genericLift
instance (Lift t,Lift a,Lift q,Lift n) => Lift (GenExpr n t a q) where
    lift = genericLift
instance Lift Value where
    lift = genericLift
instance (Lift expr) => Lift (RecordExpr expr) where
    lift = genericLift

instance IsRawExpr (AbsExpr InternalName Type HOQuantifier) where
instance IsExpr (AbsExpr Name Type HOQuantifier) where
instance HasExpr (AbsExpr Name Type HOQuantifier) where




instance NFData CastType where
instance (NFData t,NFData q,NFData n) => NFData (AbsDef n t q)
instance NFData Value
instance (NFData t,NFData q,NFData n,NFData a) => NFData (GenExpr n t a q)
instance (NFData expr) => NFData (RecordExpr expr)

instance Serialize CastType where
instance (Serialize n,Serialize q,Serialize t,Serialize a)
    => Serialize (GenExpr n t a q) where
instance (Serialize expr)
    => Serialize (RecordExpr expr) where
instance Serialize Value where
instance (Serialize n,Serialize q,Serialize t) 
    => Serialize (AbsDef n t q) where

makePrisms ''GenExpr
makePrisms ''RecordExpr

_Arguments :: (Eq n,Eq a) => AbsFun n a -> Prism' (GenExpr n t a q) [GenExpr n t a q]
_Arguments f = _FunApp.swapped.aside (only f).iso fst (,())
