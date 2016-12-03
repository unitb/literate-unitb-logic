{-# LANGUAGE TemplateHaskell #-}
module Logic.Expr.Prism 
    ( module Logic.Names 
    , module Logic.Expr.Prism 
    , fun )
where

    -- Modules
import Logic.Expr.Classes
import Logic.Expr.Expr
import Logic.Names

    -- Libraries
import Control.Lens hiding (uncons)

import Data.Functor.Contravariant
import Data.List.Lens
import Data.Maybe
import Data.String.Utils

import Language.Haskell.TH hiding (Name)
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Utils

fun :: QuasiQuoter
fun = QuasiQuoter 
        { quoteExp  = funPrism . makePattern
        , quoteType = undefined
        , quotePat  = funPat
        , quoteDec  = undefined }

{-# INLINE selectFun #-}
selectFun :: Eq n => n -> Traversal' (GenExpr n t a q) [GenExpr n t a q]
selectFun x = _FunApp . selectFun' x

selectFun' :: Eq n => n -> Traversal' (AbsFun n a,[GenExpr n t a q]) [GenExpr n t a q]
selectFun' fn f (fn',args') | fn == (fn'^.name) = (fn',) <$> f args'
                            | otherwise         = pure (fn',args')

matchLength :: Int 
            -> ( [GenExpr n t a q] -> k )
            -> Fold [GenExpr n t a q] k
matchLength recSize f = filtered ((recSize ==) . length) . to f

zipRecord' :: [Maybe String] -> ExpQ
zipRecord' args = 
        [e| matchLength ($recSize) (\_args -> $(myLet)) |]
    where
        recSize = litE $ integerL $ fromIntegral $ length fieldPos
        decs = map (binding . snd) fieldPos
        decs :: [DecQ]
        binding n = valD (varP $ mkName $ "x" ++ show n) 
                         (normalB [e| $(varE $ mkName "_args") !! $(litE $ integerL $ fromIntegral n) |]) []
        myLet = letE decs $ tupE [ varE (mkName $ "x" ++ show i) | (_,i) <- fieldPos ]
        fieldPos = mapMaybe (sequenceOf _1) $ zip args [0..]
        (n,t,a,q) = ("n","t","a","q") & each %~ (varT . mkName)
        -- recType  = appsT $ tupleT (length fieldPos) : replicate (length fieldPos) [t| GenExpr $n $t $a $q |]

funPrism :: Pattern -> ExpQ 
funPrism (Pattern f args) = [e| selectFun (fromName f) . $(zipRecord' args) |]

fieldTuple :: [String] -> PatQ
fieldTuple kw = tupP $ map (varP . mkName) kw

tuplePrism :: Pattern -> PatQ
tuplePrism (Pattern _ args) = [p| Just $(fieldTuple $ catMaybes args) |]

data Pattern = Pattern Name [Maybe String]

makePattern :: String -> Pattern
makePattern str = Pattern kw' args''
    where
        inside = fromMaybe (error "expecting parenthesis around S-expression")
                    $ strip str^?prefixed "(".suffixed ")"
        (kw,args) = fromMaybe (error "expecting at least one keyword")
                    $ inside^?partsOf worded._Cons
        args' = fromMaybe (error "field names should start with '$'")
                    $ args^?below (prefixed "$")
        kw' :: Name
        kw' = either (error . unlines) id $ isZ3Name kw
        args'' = map (^? filtered (/= "_")) args'

funPat :: String -> PatQ
funPat str = viewP 
        [e| preview $(funPrism pat) |] 
        (tuplePrism pat)
    where
        pat = makePattern str
