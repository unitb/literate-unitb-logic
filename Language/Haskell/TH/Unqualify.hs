module Language.Haskell.TH.Unqualify where

    -- Libraries
import Control.Lens hiding (lifted,Context,Const)
import Control.Monad.State

import Language.Haskell.TH.Lens
import Language.Haskell.TH.Syntax hiding (Type,Name)
import qualified Language.Haskell.TH.Syntax as TH 

unqualifyE :: Exp -> Exp
unqualifyE = transform $ execState $ do
            _VarE %= dropQual
            _ConE %= dropQual
            _SigE._2 %= unqualifyT

unqualifyT :: TH.Type -> TH.Type
unqualifyT = transform $ execState $ do
            _ConT %= dropQual

unqualifyP :: Pat -> Pat
unqualifyP = transform $ execState $ do
            _VarP %= dropQual
            _ConP._1 %= dropQual
            _ViewP._1 %= unqualifyE

dropQual :: TH.Name -> TH.Name
dropQual (TH.Name b _) = TH.Name b NameS

