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
import Agda.TypeChecking.InstanceArguments (findInstance)
import Agda.TypeChecking.ProjectionLike (reduceProjectionLike)
import Agda.TypeChecking.Reduce (instantiate, reduce)
import Agda.TypeChecking.Substitute (TelV (..))
import Agda.TypeChecking.Telescope (telView)
import Agda2Hs.AgdaUtils (decify, findInstance')
import Agda2Hs.Compile.Term (compileTerm)
import Agda2Hs.Compile.Type (compileDomType, compileType)
import Agda2Hs.Compile.Utils (agda2hsErrorM, getInlineSymbols)
import Agda2Hs.Language.Haskell (constrainType, qualifyType)
import qualified Agda2Hs.Language.Haskell as Hs
import Control.Applicative
import Control.Monad (guard, when)
import Control.Monad.State (MonadState (state), StateT (StateT, runStateT), modify)
import Data.Bifunctor (Bifunctor (second), bimap, first)
import Data.Foldable (foldrM)
import Data.Functor ((<&>))
import Data.Maybe (mapMaybe)

fromFoldable :: (Foldable f, Monad m) => f a -> ListT m a
fromFoldable = foldr consListT nilListT

haskellifyName :: NameParts -> String
haskellifyName =
  foldr
    ( \case
        Hole -> ("_" ++)
        Id x -> (map (\case '-' -> '_'; c -> c) x ++)
    )
    ""

compileLaws :: Definition -> C [Hs.Decl ()]
compileLaws def = sequenceListT $ do
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
  guard $ (argInfoHiding . domInfo $ f) == NotHidden
  lift . reportSDoc "rp" 10 $ text "f: " <+> pretty f
  fieldVal <- liftTCM . infer $ Def (defName def) [Proj ProjSystem $ unDom f]
  lift . reportSDoc "rp" 10 $ text "q: " <+> prettyTCM fieldVal
  let prop_name = Hs.Ident () . ("prop_" ++) . haskellifyName . nameNameParts . nameCanonical . qnameName . unDom $ f
  TelV ts ty <- telView fieldVal
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
    decTy <- compileType $ unEl decTy
    pure (decTy, decExp)
  lift . reportSDoc "rp" 10 $ text "e: " <+> pshow exp
  ty <- lift $ typeSig ts decTy
  fromFoldable
    [ Hs.TypeSig () [prop_name] ty
    , Hs.FunBind () [Hs.Match () prop_name (pats ts) (Hs.UnGuardedRhs () exp) empty]
    ]
 where
  typeSig :: Tele (Dom Type) -> Hs.Type () -> C (Hs.Type ())
  typeSig ts ty = foldrM aux ty (telToList ts)
   where
    aux a ty =
      compileDomType (fst . unDom $ a) (snd <$> a) <&> \case
        DomType _ hsA -> Hs.TyFun () hsA ty
        DomConstraint hsA -> constrainType hsA ty
        DomDropped -> ty
        DomForall Nothing -> ty
        DomForall (Just hsA) -> qualifyType hsA ty

  pats :: Tele (Dom Type) -> [Hs.Pat ()]
  pats = foldr aux [] . telToList
   where
    aux :: Dom (ArgName, Type) -> [Hs.Pat ()] -> [Hs.Pat ()]
    aux Dom{domInfo, unDom = (name, _)} pats =
      if argInfoHiding domInfo == NotHidden
        then Hs.PVar () (Hs.Ident () name) : pats
        else pats
