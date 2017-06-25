{-# LANGUAGE LambdaCase, CPP
        , TypeFamilies
        , TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Logic.Expr.Type where

    -- Modules
import Logic.Expr.Classes as Expr
import Logic.Expr.PrettyPrint
import Logic.Names

    -- Libraries
import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding (elements,rewriteM)
import Control.Monad.Reader
import Control.Precondition

import           Data.Data
import           Data.Void
import           Data.Hashable
import           Data.List
import qualified Data.Map as M
-- import qualified Data.Set as S
import           Data.Serialize

import           GHC.Generics.Instances

import Language.Haskell.TH.Syntax hiding (Name,Type)

import           Test.QuickCheck
import           Test.QuickCheck.ZoomEq

import           Text.Printf.TH

import           Utilities.Functor

data GenericType' v = 
        Gen !Sort ![GenericType' v] 
        | GENERIC v
    deriving (Eq,Ord,Typeable,Generic,Data,Show,Functor,Foldable,Traversable)

-- type FOType      = FOT !Sort ![FOType]
    -- deriving (Eq, Ord, Typeable, Generic, Show)

data Sort =
        BoolSort | IntSort | RealSort 
        | RecordSort !(M.Map Field ())
        | DefSort 
            !Name            -- Latex name
            !InternalName    -- Type name
            ![Name]          -- Generic Parameter
            !GenericType     -- Type with variables
        | Sort !Name !InternalName !Int
        | Datatype 
            [Name]      -- Parameters
            Name        -- type name
            [(Name, [(InternalName,GenericType)])] 
                        -- alternatives and named components
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

newtype Field = Field Name
    deriving (Eq, Ord, Show, Typeable, Data, Generic)

type GenericType = GenericType' InternalName
type Type = GenericType
type FOType = GenericType' Void

newtype TypeVar = TypeVar { unTypeVar :: Int } 
    deriving (Eq, Ord, Show, Generic, Enum)

data Unif v = UnifVar TypeVar | FreeVar v
    deriving (Functor,Foldable,Traversable
             ,Eq,Show,Ord,Generic)

-- makePrisms ''FOType
makePrisms ''GenericType'
makePrisms ''Sort
makePrisms ''TypeVar
makePrisms ''Unif

type OpenType v = GenericType' (Unif v)

typeVar :: (TypeVar -> r) -> (v -> r) -> Unif v -> r
typeVar f _ (UnifVar i) = f i
typeVar _ f (FreeVar x) = f x


newtype SubType' v = SubType { unSubType :: GenericType' v } 
    deriving (Eq,Ord,Typeable,Generic,Data,Show
             ,PrettyPrintable,Hashable
             ,Functor,Foldable,Traversable
             ,Applicative,Monad)

type SubType = SubType' InternalName

instance Rewrapped (SubType' v) (SubType' u) where
instance Wrapped (SubType' v) where
    type Unwrapped (SubType' v) = GenericType' v
    _Wrapped' = iso unSubType SubType

-- referenced_types :: FOType -> S.Set FOType
-- referenced_types t@(FOT _ ts) = S.insert t $ S.unions $ map referenced_types ts

class TypeOf a ~ TypeOf (TypeOf a) => Typed a where
    type TypeOf a :: *
    type_of :: a -> TypeOf a
    types :: Traversal' a (TypeOf a)

instance Typed (GenericType' v) where
    type TypeOf (GenericType' v) = GenericType' v
    type_of = id
    types _ = pure

instance Typed (SubType' v) where
    type TypeOf (SubType' v) = SubType' v
    type_of = id
    types _ = pure

-- class (Ord a, Tree a, PrettyPrintable a, Show a
--         , TypeAnnotationPair a a
--         , Typed a, TypeOf a ~ a, Typeable a
--         , Hashable a ) 
class (Typed t,TypeOf t ~ t,Typeable t,Tree t,PrettyPrintable t,Ord t) 
        => TypeSystem t where
    make_type :: Sort -> [t] -> t
    _FromSort :: Prism' t (Sort,[t])

class (TypeSystem t,HasTypeVars t) => IsPolymorphic t where
    genericType' :: Iso' t GenericType
    _GENERIC'  :: Prism' t InternalName

genericType :: (IsPolymorphic a,IsPolymorphic b) 
            => Iso a b GenericType GenericType
genericType = 
         withIso genericType' $ \f _ -> 
         withIso genericType' $ \_ g -> 
            iso f g

instance IsPolymorphic GenericType where
    genericType' = id
    _GENERIC'  = _GENERIC
instance IsPolymorphic SubType where
    genericType' = _Wrapped
    _GENERIC'  = _Wrapped._GENERIC'

class (Typed a,Plated a) => HasTypeVars a where
    generics :: Traversal' a InternalName
    -- variables :: Traversal' a InternalName
    -- _VARIABLE' :: Prism' a InternalName
    default generics :: HasTypeVars (TypeOf a) => Traversal' a InternalName
    generics = types.generics
    -- default variables :: HasTypeVars (TypeOf a) => Traversal' a InternalName
    -- variables = types.variables
    -- generics x  = S.fromList $ genericsList x
    -- genericsList x  = concatMap genericsList $ S.toList $ types_of x
    -- variables x = S.unions $ map variables $ S.toList $ types_of x

instance HasTypeVars (GenericType) where
    generics f (GENERIC s) = GENERIC <$> f s
    -- generics _f t@(VARIABLE _) = pure t
    generics f (Gen s ts) = Gen s <$> (traverse.generics) f ts
    -- variables f (VARIABLE s) = VARIABLE <$> f s
    -- variables _f t@(GENERIC _) = pure t
    -- variables f (Gen s ts) = Gen s <$> (traverse.variables) f ts
    -- _VARIABLE' = _VARIABLE
    -- genericsList (GENERIC s)     = [s]
    -- genericsList (VARIABLE _)    = []
    -- genericsList (Gen _ ts) = concatMap genericsList ts
    -- variables (VARIABLE s)       = S.singleton s
    -- variables (GENERIC _)        = S.empty
    -- variables (Gen _ ts) = S.unions $ map variables ts
    -- types_of t = S.singleton t

instance HasTypeVars SubType where
    generics   = _Wrapped.generics
    -- variables  = _Wrapped.variables
    -- _VARIABLE' = _

-- class TypeAnnotationPair a b where
--     strippedType :: b -> a

-- instance TypeAnnotationPair () t where
--     strippedType _ = ()

-- instance TypeAnnotationPair (SubType' v) (SubType' v) where
--     strippedType = id
    
-- instance TypeAnnotationPair (GenericType' v) (GenericType' v) where
--     strippedType = id

-- instance TypeAnnotationPair FOType FOType where
--     strippedType = id

class (Ord v,Typeable v,PrettyPrintable v) => IsTypeVar v where

instance IsTypeVar InternalName where
instance IsTypeVar Void where
instance IsTypeVar v => IsTypeVar (Unif v) where

instance IsTypeVar v 
        => TypeSystem (SubType' v) where
    make_type ss = SubType . make_type ss . map unSubType
    _FromSort f = dimap unSubType (fmap SubType) $ _FromSort $ dimap 
            (_2.traverse %~ SubType) 
            (mapped._2.traverse %~ unSubType) f
instance IsTypeVar v 
        => TypeSystem (GenericType' v) where
    make_type ss = Gen ss . evalList
    _FromSort    = _Gen . mapping (iso id evalList)

-- instance Typed FOType where
--     type TypeOf FOType = FOType
--     type_of = id
--     types _ = pure

-- instance TypeSystem FOType where
--     make_type ss = Gen ss . evalList
--     _FromSort   = _Gen . mapping (iso id evalList)

instance PrettyPrintable v => PrettyPrintable (Unif v) where
    pretty (UnifVar i) = "@" ++ show i
    pretty (FreeVar x) = pretty x

instance PrettyPrintable Sort where
    pretty (RecordSort m) = [s|{ %s }|] $ intercalate ", " 
                $ zipWith (\f -> [s|'%s :: a%d|] (fieldName f)) (M.keys m) [0..]
    pretty ss = render $ ss^.name

-- instance Hashable FOType where
instance Hashable TypeVar where
instance Hashable v => Hashable (Unif v) where
instance Hashable v => Hashable (GenericType' v) where
instance Hashable Sort where
instance Hashable Field where

instance Typed () where
    type TypeOf () = ()
    type_of = id
    types _ = pure

instance TypeSystem () where
    make_type _ _ = ()
    _FromSort = prism' (const ()) (const Nothing)

instance Plated (SubType' t) where
    plate f (SubType t) = SubType <$> plate (_Unwrapped' f) t
instance PrettyPrintable v => Tree (SubType' v) where
    as_tree' = as_tree' . unSubType
    -- {-# INLINABLE rewriteM #-}
    -- rewriteM = _Wrapped'.rewriteM._Unwrapped'
instance Plated (GenericType' t) where
    {-# INLINABLE plate #-}
    plate f (Gen ss ts) = do
            Gen ss <$> traverse f ts
    plate _ x@(GENERIC _) = pure x
instance PrettyPrintable v => Tree (GenericType' v) where
    as_tree' (Gen ss ts) = cons_to_tree ss ts
    as_tree' (GENERIC x)   = return $ Str $ "'" ++ pretty x

instance Applicative GenericType' where
    pure = GENERIC
    (<*>) = ap
instance Monad GenericType' where
    Gen s ts  >>= f = Gen s $ map (>>= f) ts
    GENERIC x >>= f = f x


-- instance Plated FOType where
--     {-# INLINABLE plate #-}
--     plate f (FOT ss ts) = FOT ss <$> traverse f ts

-- instance Tree FOType where
--     as_tree' (FOT ss ts) = cons_to_tree ss ts

instance Lift GenericType where
    lift = genericLift

as_generic :: FOType -> GenericType' a
as_generic = fmap absurd

cons_to_tree :: Tree a => Sort -> [a] -> Reader (OutputMode n) StrList
cons_to_tree ss [] = do
    opt <- ask
    let n = case opt of
                ProverOutput -> render $ z3_name ss
                UserOutput -> render $ ss^.name
    return $ Str n
cons_to_tree ss ts = do
    opt <- ask
    let n = case opt of
                ProverOutput -> render $ z3_name ss
                UserOutput -> render $ ss^.name
    return $ Expr.List (Str n : map as_tree ts)

typeParams :: Sort -> Int
typeParams (RecordSort m) = M.size m
typeParams BoolSort = 0
typeParams IntSort  = 0
typeParams RealSort = 0
typeParams (Sort _ _ n) = n
typeParams (DefSort _ _ ps _) = length ps
typeParams (Datatype xs _ _)  = length xs

-- instance PrettyPrintable FOType where
--     pretty (FOT ss []) = (render $ z3_name ss)
--     pretty (FOT t ts) = [s|%s %s|] (render $ t^.name) (show $ map Pretty ts)

instance PrettyPrintable Field where
    pretty (Field n) = pretty n

instance PrettyPrintable v => PrettyPrintable (GenericType' v) where
    pretty (GENERIC n)        = "'" ++ pretty n 
    pretty (Gen (RecordSort m) xs) = [s|{ %s }|] $ intercalate ", " 
                $ zipWith (\f t -> [s|'%s :: %s|] (fieldName f) (pretty t)) (M.keys m) xs
    pretty (Gen ss []) = render $ ss^.name
    pretty (Gen t ts) = [s|%s %s|] (render $ t^.name) (show $ map Pretty ts)

recordName :: M.Map Field a -> Name
recordName m = makeZ3Name $ "Record-" ++ intercalate "-" (map fieldName $ M.keys m)

accessor :: Field -> String
accessor = render . accessorName

accessorName :: Field -> InternalName
accessorName (Field n) = addPrefix "field" $ asInternal n

fieldName :: Field -> String
fieldName (Field n) = [s|%s|] (render n)

_Params :: TypeSystem t => Sort -> Prism' t [t]
_Params s = _FromSort.swapped.aside (only s).iso fst (,())

instance HasName Sort Name where
    name = to $ \case 
        RecordSort m   -> recordName m
        (Sort x _ _) -> x
        (DefSort x _ _ _) -> x
        (Datatype _ x _)  -> x
        BoolSort   -> makeName "\\Bool"
        IntSort    -> makeName "\\Int"
        RealSort   -> makeName "\\Real"

instance Named Sort where
    type NameOf Sort = Name
    decorated_name' ss = do
        opt <- ask
        case opt of
            ProverOutput -> return $ z3_name ss
            UserOutput -> return $ ss^.name

        -- TODO: make BoolSort, IntSort, RealSort into 
        -- the Sort datatype with a 'builtin' flag
    z3_name (Sort _ x _) = x
    z3_name (DefSort _ x _ _) = x
    z3_name (Datatype _ x _)  = asInternal x
    z3_name (RecordSort m) = asInternal $ recordName m
    z3_name BoolSort   = [smt|Bool|]
    z3_name IntSort    = [smt|Int|]
    z3_name RealSort   = [smt|Real|]

instance Lift Sort where
    lift = genericLift

instance Lift Field where
    lift = genericLift

pair_sort :: Sort
pair_sort = -- Sort "Pair" "Pair" 2
               Datatype [[smt|a|],[smt|b|]] 
                    ([smt|Pair|])
                    [ ([smt|pair|], 
                        [ ([smt|first|],  gA)
                        , ([smt|second|], gB) ]) ]


pair_type :: TypeSystem t => t -> t -> t
pair_type x y = make_type pair_sort [x,y]

null_sort :: Sort
null_sort = Datatype [] ([smt|Null|]) [ ([smt|null|], []) ] 

null_type :: TypeSystem t => t
null_type = make_type null_sort []

maybe_sort :: Sort
maybe_sort   = Datatype [[smt|a|]] ([smt|Maybe|])
                    [ ([smt|Just|], [([smt|fromJust|], gA)])
                    , ([smt|Nothing|], []) ]

maybe_type :: TypeSystem t => t -> t
maybe_type t = make_type maybe_sort [t]

guarded_sort :: Sort
guarded_sort = DefSort [smt|guarded|] [smt|guarded|] [[smt|a|]] (maybe_type gA)

guarded_type :: TypeSystem t => t -> t
guarded_type = make_type guarded_sort . pure

fun_sort :: Sort
fun_sort = make DefSort "\\pfun"
        "pfun" [[smt|a|],[smt|b|]] (array gA (maybe_type gB))

fun_type :: TypeSystem t => t -> t -> t
fun_type t0 t1 = make_type fun_sort [t0,t1] --ARRAY t0 t1

bool :: TypeSystem t => t
bool = make_type BoolSort []
    
array_sort :: Sort
array_sort = make Sort "Array" "Array" 2

array :: TypeSystem t => t -> t -> t
array t0 t1 = make_type array_sort [t0,t1]

set_sort :: Sort
set_sort = make DefSort "\\set" "set" [[smt|a|]] (array gA bool)

set_type :: TypeSystem t => t -> t
set_type t = make_type set_sort [t]

record_sort :: M.Map Field t -> Sort
record_sort fields = RecordSort $ () <$ fields

record_type :: TypeSystem t => M.Map Field t -> t
record_type fields = make_type (record_sort fields) (M.elems fields)

_ElementType :: TypeSystem t => Prism' t t
_ElementType = _FromSort.swapped.below (only set_sort).first._Cons.below _Empty.first
    where
        first = iso fst (,())

elementType :: (TypeSystem t,Pre) => t -> t
elementType t = fromJust' $ t^?_ElementType

foldSorts :: TypeSystem t => Fold t Sort
foldSorts = _FromSort.(\f (ss,ts) -> liftA2 (,) (f ss) ((traverse.foldSorts) f ts))

int :: TypeSystem t => t
int  = make_type IntSort []

real :: TypeSystem t => t
real = make_type RealSort []

instance Arbitrary Field where
    arbitrary = genericArbitrary

instance Arbitrary Sort where
    arbitrary = oneof
        [ pure BoolSort 
        , pure IntSort 
        , pure RealSort 
        , Sort <$> arbitrary <*> arbitrary <*> elements [0..5]
        ]
    shrink = genericShrink

gA :: IsPolymorphic t => t
gA = GENERIC [smt|a|]^.from genericType'

gB :: IsPolymorphic t => t
gB = GENERIC [smt|b|]^.from genericType'

gC :: IsPolymorphic t => t
gC = GENERIC [smt|c|]^.from genericType'

z3Sort :: Pre 
       => String -> String -> Int -> Sort
z3Sort n0 n1 = Sort (fromString'' n0) (z3Name n1)

z3DefSort :: Pre 
          => String -> String -> [String] -> GenericType -> Sort
z3DefSort n0 n1 ps = DefSort (fromString'' n0) (fromString'' n1) (fromString'' <$> ps)

z3GENERIC :: Pre
          => String -> GenericType
z3GENERIC = GENERIC . fromString''

z3_decoration :: Tree t => t -> String
z3_decoration t = runReader (z3_decoration' t) ProverOutput

z3_decoration' :: Tree t => t -> Reader (OutputMode n) String
z3_decoration' t = do
        opt <- ask 
        case opt of
            ProverOutput -> f <$> as_tree' t
            UserOutput -> return ""
    where
        f (Expr.List ys) = [s|@Open%s@Close|] xs
            where xs = concatMap f ys :: String
        f (Str y)   = [s|@@%s|] y

instance Serialize Sort where
instance Serialize Type where
instance Serialize Field where

instance ZoomEq Field where
instance ZoomEq Sort where
instance ZoomEq GenericType where

#if !(MIN_VERSION_QuickCheck(2,8,2))
instance (Arbitrary k,Arbitrary a,Ord k) => Arbitrary (M.Map k a) where
    arbitrary = M.fromList <$> arbitrary
    shrink = fmap M.fromList . shrink . M.toList
#endif

instance Arbitrary GenericType where
    arbitrary = oneof (
                [ return bool
                , return int
                , return real
                ] ++ concat (take 2 $ repeat
                [ do
                    t0 <- arbitrary
                    t1 <- arbitrary
                    return $ array t0 t1
                , oneof gen_prm
                , do
                    ss  <- oneof sorts
                    ts <- case ss of
                        RecordSort m -> 
                            replicateM (M.size m) arbitrary
                        Sort _ _ n -> 
                            replicateM n arbitrary
                        DefSort _ _ args _ -> 
                            replicateM (length args) arbitrary
                        IntSort -> 
                            return []
                        RealSort ->
                            return []
                        BoolSort -> 
                            return []
                        Datatype _ _ _ -> error "Type.arbitrary: impossible"
                    return $ Gen ss ts
                , do
                    t <- arbitrary
                    return $ set_type t
                , do
                    t0 <- arbitrary
                    t1 <- arbitrary
                    return $ fun_type t0 t1
                ] ) )
        where
            sorts = map return
                [ make Sort "A" "A" 0
                , make Sort "B" "B" 1
                , make Sort "C" "C" 1
                , make Sort "D" "D" 2
                , make DefSort "E" "E" 
                            [ [smt|a|]
                            , [smt|b|]] $ array gA gB
                , BoolSort
                , IntSort
                , RealSort
                ]
            gen_prm = map return
                [ gA
                , gB
                , gC
                ]
    shrink = genericShrink

instance NFData FOType
instance NFData GenericType
instance NFData Sort
instance NFData Field
