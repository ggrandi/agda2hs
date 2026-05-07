module Agda2Hs.Compile.Laws (compileLaws) where

import Control.Monad (filterM, unless, when)
import Control.Monad.Reader (asks, local)

import Data.Foldable (toList)
import qualified Data.HashMap.Strict as HMap
import Data.List (nub, singleton, uncons)
import Data.Maybe (isNothing, mapMaybe)

import Agda.Compiler.Backend
import Agda.Compiler.Common (curDefs, sortDefs)

import Agda.Syntax.Common hiding (Ranged)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal hiding (QName)
import Agda.Syntax.Internal.Pattern (patternToTerm)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (resolveName)

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute (Apply (applyE), absApp, absBody, apply)
import Agda.TypeChecking.Telescope (mustBePi, piApplyM)

import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Lens
import Agda.Utils.List (headWithDefault)
import Agda.Utils.ListT
import Agda.Utils.Monad (ifNotM, lift)

import Agda2Hs.AgdaUtils
import Agda2Hs.Compile.Function
import Agda2Hs.Compile.Name
import Agda2Hs.Compile.Term
import Agda2Hs.Compile.Type
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils

import Agda.Syntax.Concrete (Name (nameNameParts))
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Utils.ListT as ListT
import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils (hsName, pp, replaceName, unQual)
import Control.Applicative
import Control.Monad.IO.Class (liftIO)
import Data.Containers.ListUtils (nubOrdOn)

fromFoldable :: (Foldable f, Monad m) => f a -> ListT m a
fromFoldable = foldr consListT nilListT

fromFoldable' :: (Foldable f, Monad m) => m (f a) -> ListT m a
fromFoldable' = runMListT . (fromFoldable <$>)

prettyNameParts :: C.NameParts -> String
prettyNameParts =
  foldr
    ( \case
        C.Hole -> ('_' :)
        (C.Id x) -> (map (\x -> if x == '-' then '_' else x) x ++)
    )
    ""

nubOrdOnListT :: (Ord b, Monad m) => (a -> b) -> ListT m a -> ListT m a
nubOrdOnListT f = fromFoldable' . (nubOrdOn f <$>) . sequenceListT

getClauseDefs :: [Clause] -> ListT C (String, ())
getClauseDefs clauses = nubOrdOnListT fst $ do
  Clause{..} <- fromFoldable clauses
  named_clause <- (unArg . fst <$>) . fromFoldable . uncons . filter (\Arg{argInfo = ArgInfo{argInfoHiding}} -> argInfoHiding == NotHidden) $ namedClausePats
  name <- case namedThing named_clause of
    ProjP _ q -> pure . prettyNameParts . nameNameParts . nameConcrete . qnameName $ q
  lift . reportSDoc "rp" 10 $ text "name: " <+> pshow name
  lift . reportSDoc "rp" 10 $ text "clause_type: " <+> pretty clauseType <+> pshow (unEl . unArg <$> clauseType)
  pure (name, ())

compileLaws :: Definition -> C [Hs.Decl ()]
compileLaws def@Defn{..} = sequenceListT $ do
  let Function{..} = theDef
  lift . reportSDoc "rp" 10 $ text "clause: " <+> pretty theDef
  liftIO . print . length $ funClauses
  (name, ty) <- getClauseDefs funClauses
  let prop_name = Hs.Ident () ("prop_" ++ name)
  pure $
    Hs.FunBind
      ()
      [ Hs.Match
          ()
          prop_name
          []
          (Hs.UnGuardedRhs () $ Hs.Con () $ Hs.UnQual () $ Hs.Ident () "True")
          Nothing
      ]

-- fromFoldable
--   [ Hs.TypeSig
--       ()
--       [prop_name]
--       (Hs.TyFun () (Hs.TyCon () $ Hs.UnQual () $ Hs.Ident () "Int") (Hs.TyCon () $ Hs.UnQual () $ Hs.Ident () "Bool"))
--   , Hs.FunBind
--       ()
--       [ Hs.Match
--           ()
--           prop_name
--           [Hs.PLit () (Hs.Signless ()) $ Hs.Int () 0 "0"]
--           (Hs.UnGuardedRhs () $ Hs.Con () $ Hs.UnQual () $ Hs.Ident () "True")
--           Nothing
--       , Hs.Match
--           ()
--           prop_name
--           [Hs.PVar () x]
--           (Hs.UnGuardedRhs () $ Hs.InfixApp () var_x (Hs.QVarOp () $ Hs.UnQual () $ Hs.Symbol () "==") var_x)
--           Nothing
--       ]
--   ]
