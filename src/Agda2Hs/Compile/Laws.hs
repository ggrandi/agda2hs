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
import Agda2Hs.Compile.Type (compileType)
import Agda2Hs.Compile.Utils (agda2hsErrorM)
import qualified Agda2Hs.Language.Haskell as Hs
import Control.Monad (forM, guard)
import Data.Foldable (foldrM)
import Data.Function ((&))
import Data.Functor (($>), (<&>))
import qualified Data.Text as T

chooseOne :: (Foldable f, Monad m) => f a -> ListT m a
chooseOne = foldr consListT nilListT

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
      -- maybe should call this one seq
      . T.replace "<*>" "zap"
      -- maybe should call this one seqLeft
      . T.replace ">>" "seq"
      . T.replace ">>=" "bind"
      . T.replace "-" "_"
      . T.pack

compileLaws :: Definition -> C [Hs.Decl ()]
compileLaws def = do
  reportSDoc "rp" 10 $ text "def: " <+> prettyTCM (defType def)
  -- TODO: inspect _defTs for applying values to the definition
  TelV _defTs defCore <- def & defType & telView
  qname <- case unEl defCore of
    Def q _ -> pure q
    x -> agda2hsErrorM $ text "expected def but got: " $+$ prettyTCM x
  reportSDoc "rp" 10 $ text "q: " <+> prettyTCM qname
  defInfo <- getConstInfo qname
  reportSDoc "rp" 10 $ text "defInfo: " <+> pretty defInfo
  defFields <- case theDef defInfo of
    RecordDefn x -> pure . _recFields $ x
    _ -> lift $ agda2hsErrorM $ text "expected to compile a record with the laws pragma but got: " $+$ pretty defInfo
  natTy <- resolveStringName "Nat" <&> (`Def` [])
  -- TODO: Use a different check for whether a field should be included as a law
  let laws = filter (\field -> argInfoHiding (domInfo field) == NotHidden) defFields
  forM laws $ \law -> do
    reportSDoc "rp" 10 $ text "f: " <+> pretty law
    fieldTy <- liftTCM $ infer (Def (defName def) [Proj ProjSystem $ unDom law])
    lawTy <- liftTCM $ applyX natTy fieldTy
    reportSDoc "rp" 10 $ text "lawTy: " <+> prettyTCM lawTy
    let law_name = law & unDom & qnameName & nameCanonical & nameNameParts & haskellifyName
    let prop_name = Hs.Ident () ("prop_" ++ law_name)
    TelV fieldTs fieldTy <- telView lawTy
    reportSDoc "rp" 10 $ text "telescope args: " <+> prettyTCM fieldTs
    decidedExp <- addContext fieldTs $ do
      decTy <- decify fieldTy
      -- Ignore the type since it can be inferred on the Haskell side and I expect it to be a Boolean
      liftTCM (findInstance' decTy) >>= \case
        Nothing -> do
          agda2hsErrorM $ "No Dec instance found for" $+$ prettyTCM fieldTy
        Just decInst -> do
          reportSDoc "rp" 10 $ text "decinst: " <+> prettyTCM decInst
          compileTerm decTy decInst
    pats <- pats fieldTs
    pure $ Hs.FunBind () [Hs.Match () prop_name pats (Hs.UnGuardedRhs () decidedExp) Nothing]
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
          newBody <- (body $>) <$> underAbstraction arg body (applyX x)
          pure $ mkPiSort arg newBody `El` Pi arg newBody
    _ -> pure ty
