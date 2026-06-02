{-# OPTIONS_GHC -W -Wno-error=all #-}

module Agda2Hs.Compile.Laws (compileLaws) where

import Agda.Compiler.Backend

import Agda.Syntax.Common hiding (Ranged)
import Agda.Syntax.Internal hiding (QName)

import Agda.TypeChecking.Pretty
import Agda.Utils.ListT
import Agda.Utils.Monad (lift)

import Agda2Hs.Compile.Types

import Agda.Syntax.Concrete (Name (nameNameParts), NamePart (..))
import Agda.Syntax.Concrete.Name (NameParts)
import Agda.TypeChecking.CheckInternal
import Agda.TypeChecking.Substitute (TelV (..), mkPiSort)
import Agda.TypeChecking.Telescope (PiApplyM (piApplyM), ifPi, telView)
import Agda2Hs.AgdaUtils (decify, findInstance', resolveStringName)
import Agda2Hs.Compile.Term (compileTerm)
import Agda2Hs.Compile.Type (compileDomType, compileType)
import qualified Agda2Hs.Language.Haskell as Hs
import Agda2Hs.Language.Haskell.Utils (constrainType, qualifyType)
import Control.Applicative (empty)
import Control.Monad (guard)
import Control.Monad.RWS (MonadWriter (tell))
import Data.Foldable (foldrM)
import Data.Functor (($>), (<&>))
import qualified Data.Text as T

{-# INLINE fromFoldable #-}
fromFoldable :: (Foldable f, Monad m) => f a -> ListT m a
fromFoldable = foldr consListT nilListT

{-# INLINE haskellifyName #-}
haskellifyName :: NameParts -> String
haskellifyName =
  replaceProblematic
    . foldr
      ( \case
          Hole -> ("_" ++)
          Id x -> (x ++)
      )
      ""
 where
  replaceProblematic :: String -> String
  replaceProblematic =
    T.unpack
      . T.replace "<$>" "fmap"
      . T.replace "<*>" "zap"
      . T.replace ">>" "seq"
      . T.replace ">>=" "bind"
      . T.replace "-" "_"
      . T.pack

compileLaws :: Definition -> C [Hs.Decl ()]
compileLaws def = sequenceListT $ do
  natTy <- liftTCM natTy
  lift . reportSDoc "rp" 10 $ text "def: " <+> pretty (defType def)
  -- lift . reportSDoc "rp" 10 . pshow . defType $ def
  (q, _) <- case unEl . defType $ def of
    Def q elims -> pure (q, elims)
    x -> do
      lift . reportSDoc "rp" 10 $ text "expected def but got: " <+> prettyTCM x
      empty
  lift . reportSDoc "rp" 10 $ text "x: " <+> prettyTCM q
  x <- getConstInfo q
  lift . reportSDoc "rp" 10 $ text "x: " <+> pretty x
  f <- case theDef x of
    RecordDefn x -> fromFoldable . _recFields $ x
    _ -> do
      lift . reportSDoc "rp" 10 $ text "expected RecordDefN but got: " <+> pretty x
      empty
  guard $ argInfoHiding (domInfo f) == NotHidden
  lift . reportSDoc "rp" 10 $ text "f: " <+> pretty f
  fieldVal <- liftTCM (infer $ Def (defName def) [Proj ProjSystem $ unDom f]) >>= liftTCM . applyX natTy
  lift . reportSDoc "rp" 10 $ text "fieldVal: " <+> prettyTCM fieldVal
  let prop_name = Hs.Ident () . ("prop_" ++) . haskellifyName . nameNameParts . nameCanonical . qnameName . unDom $ f
  TelV ts ty <- telView fieldVal
  lift . reportSDoc "rp" 10 $ text "telescope args: " <+> prettyTCM ts
  (decTy, exp) <- lift $ addContext ts $ do
    decTy <- decify ty
    decExp <-
      liftTCM (findInstance' decTy) >>= \case
        Nothing -> do
          reportSDoc "rp" 10 $ "No Dec instance found for" <+> prettyTCM decTy
          pure $ Hs.Con () $ Hs.UnQual () $ Hs.Ident () "False"
        Just decInst -> do
          reportSDoc "rp" 10 $ text "decinst: " <+> prettyTCM decInst
          compileTerm decTy decInst
    (,decExp) <$> compileType (unEl decTy)
  -- ty <- lift $ typeSig ts decTy
  pats <- lift $ pats ts
  fromFoldable
    [ -- Hs.TypeSig () [prop_name] ty ,
      Hs.FunBind () [Hs.Match () prop_name pats (Hs.UnGuardedRhs () exp) empty]
    ]
 where
  pats :: Tele (Dom Type) -> C [Hs.Pat ()]
  pats = foldrM aux [] . telToList
   where
    aux :: Dom (ArgName, Type) -> [Hs.Pat ()] -> C [Hs.Pat ()]
    aux Dom{domInfo, unDom = (name, ty)} pats =
      if argInfoHiding domInfo /= NotHidden
        -- should be fine since all the type variables should be concrete
        then pure pats
        else do
          compiledTy <- compileType (unEl ty)
          let typedVar = Hs.PatTypeSig () (Hs.PVar () (Hs.Ident () name)) compiledTy
          (ifPi $ unEl ty)
            ( const . const $ do
                pure $ Hs.PApp () (Hs.UnQual () $ Hs.Ident () "Fun") [Hs.PWildCard (), typedVar] : pats
            )
            (const $ pure $ typedVar : pats)

  -- \| Applies @x@ to all pi types of the form `(x : Set) -> ...`
  applyX :: Term -> Type -> TCM Type
  applyX x ty = case unEl ty of
    Pi arg body
      -- currently it just checks `Type₀` since agda2hs expects most types to be there
      | unEl (unDom arg) == Sort (Univ UType (Max 0 [])) -> do
          appliedTy <- piApplyM ty x
          applyX x appliedTy
      | otherwise -> do
          reportSDoc "rp" 100 $ text "N applyX: " <+> prettyTCM arg
          x <- (body $>) <$> underAbstraction arg body (applyX x)
          pure $ mkPiSort arg x `El` Pi arg x
    _ -> pure ty

  natTy :: TCM Term
  natTy = do
    qn <- resolveStringName "Agda.Builtin.Nat.Nat"
    pure (Def qn [])
