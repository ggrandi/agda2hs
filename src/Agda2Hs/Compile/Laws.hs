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
import Agda.TypeChecking.ProjectionLike (reduceProjectionLike)
import Agda.TypeChecking.Reduce (instantiate, reduce)
import Agda.TypeChecking.Substitute (TelV (..))
import Agda.TypeChecking.Telescope (telView)
import Agda2Hs.AgdaUtils (decify, findInstance')
import Agda2Hs.Compile.Term (compileTerm)
import Agda2Hs.Compile.Type (compileDomType)
import Agda2Hs.Compile.Utils (agda2hsErrorM, getInlineSymbols)
import Agda2Hs.Language.Haskell (constrainType, qualifyType)
import qualified Agda2Hs.Language.Haskell as Hs
import Control.Applicative
import Control.Monad (guard, when)
import Control.Monad.State (MonadState (state), StateT (StateT, runStateT), modify)
import Data.Bifunctor (Bifunctor (second), bimap, first)
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

typeToProp :: Type -> C (Hs.Type (), ([Hs.Pat ()], Hs.Exp ()))
typeToProp ty = do
  reportSDoc "rp" 10 $ text "compiling term:" <+> prettyTCM ty

  v <- instantiate . unEl $ ty

  toInline <- getInlineSymbols
  v <- locallyReduceDefs (OnlyReduceDefs toInline) $ reduce v

  let bad s t =
        agda2hsErrorM $
          vcat
            [ text "cannot compile" <+> text (s ++ ":")
            , nest 2 $ prettyTCM t
            ]

  v <- reduceProjectionLike v
  case v of
    (Pi a b) -> do
      reportSDoc "rp" 13 $
        text "Handling pi type ("
          <+> prettyTCM (absName b)
          <+> text ":"
          <+> prettyTCM a
          <+> text ") -> "
          <+> underAbstraction
            a
            b
            prettyTCM
      ( `bimap`
          if (argInfoHiding . domInfo $ a) == NotHidden
            then first ((Hs.PVar () $ Hs.Ident () $ absName b) :)
            else id
        )
        <$> ( compileDomType (absName b) a <&> \case
                DomType _ hsA -> Hs.TyFun () hsA
                DomConstraint hsA -> constrainType hsA
                DomDropped -> id
                DomForall Nothing -> id
                DomForall (Just hsA) -> qualifyType hsA
            )
        <*> underAbstraction a b typeToProp
    -- second (Hs.TyFun () dTy) <$> underAbstraction a b aux
    x@(Def f es) -> do
      reportSDoc "rp" 10 $ text "def: " <+> prettyTCM x
      decTy <- decify ty
      decExp <-
        liftTCM (findInstance' decTy) >>= \case
          Nothing -> agda2hsErrorM $ "No Dec instance found for" <+> prettyTCM decTy
          Just decInst -> do
            reportSDoc "rp" 10 $ text "decinst: " <+> prettyTCM decInst
            compileTerm decTy decInst
      pure (Hs.TyCon () $ Hs.UnQual () $ Hs.Ident () "Bool", ([], decExp))
    x -> bad "unhandled other" x

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
  (ty, (args, exp)) <- lift $ typeToProp fieldVal
  fromFoldable
    [ Hs.TypeSig () [prop_name] ty
    , Hs.FunBind () [Hs.Match () prop_name args (Hs.UnGuardedRhs () exp) empty]
    ]
