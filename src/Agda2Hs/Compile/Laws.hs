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
import Agda.TypeChecking.Telescope (telView)
import Agda2Hs.AgdaUtils (decify, findInstance')
import Agda2Hs.Compile.Term (compileTerm)
import Agda2Hs.Compile.Utils (agda2hsErrorM, getInlineSymbols)
import qualified Agda2Hs.Language.Haskell as Hs
import Control.Applicative
import Agda.TypeChecking.Substitute (TelV(..))

fromFoldable :: (Foldable f, Monad m) => f a -> ListT m a
fromFoldable = foldr consListT nilListT

-- fromFoldable' :: (Foldable f, Monad m) => m (f a) -> ListT m a
-- fromFoldable' = lift >=> fromFoldable

haskellifyName :: NameParts -> String
haskellifyName =
  foldr
    ( \case
        Hole -> ("_" ++)
        Id x -> (map (\case '-' -> '_'; c -> c) x ++)
    )
    ""

-- telToProperties :: Telescope -> ListT C (ArgName, Type)
-- telToProperties x = do
--   x <- fromFoldable . telToList $ x
--   guard ((argInfoHiding . domInfo $ x) == NotHidden)
--   let (name, ty) = unDom x
--   pure (haskellifyName name, ty)

typeToProp :: Type -> ListT C (Hs.Decl ())
typeToProp v = do
  reportSDoc "rp" 10 $ text "compiling term:" <+> prettyTCM v

  v <- instantiate . unEl $ v

  toInline <- lift getInlineSymbols
  v <- locallyReduceDefs (OnlyReduceDefs toInline) $ reduce v

  let bad s t =
        agda2hsErrorM $
          vcat
            [ text "cannot compile" <+> text (s ++ ":")
            , nest 2 $ prettyTCM t
            ]

  v <- reduceProjectionLike v
  case v of
    x@(Pi d a) -> do
      let a' = unAbs a
      reportSDoc "rp" 10 $ text "handling pi"
      typeToProp a'
    x@(Def f es) -> do
      reportSDoc "rp" 10 $ text "def: " <+> prettyTCM x
      -- reportSDoc "rp" 10 $ text "def: " <+> pshow x
      ty <- defType <$> getConstInfo f
      empty
    x -> do
      reportSDoc "rp" 10 $ text "unhandled: " <+> pshow x
      empty

--   Def _ _ -> lift $ bad "Def" v
--   Con{} -> lift $ bad "Con" v
--   Var{} -> lift $ bad "Var" v
--   Lit{} -> lift $ bad "Lit" v
--   Lam{} -> lift $ bad "Lam" v
--   Pi x y -> do
--     reportSDoc "rp" 10 $ text "x:" <+> prettyTCM x
--     reportSDoc "rp" 10 $ text "y:" <+> prettyTCM y
--     lift $ bad "function type" v
--   v@Sort{} -> lift $ bad "sort type" v
--   v@Level{} -> lift $ bad "level term" v
--   v@MetaV{} -> lift $ bad "unsolved metavariable" v
--   v@DontCare{} -> lift $ bad "irrelevant term" v
--   v@Dummy{} -> lift $ bad "dummy term" v

-- getConstInfo
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
    RecordDefn x -> (unDom <$>) . fromFoldable . _recFields $ x
    _ -> do
      lift . reportSDoc "rp" 10 $ text "expected RecordDefN but got: " <+> pretty x
      empty
  lift . reportSDoc "rp" 10 $ text "f: " <+> pretty f
  fieldVal <- liftTCM . infer $ Def (defName def) [Proj ProjSystem f]
  lift . reportSDoc "rp" 10 $ text "q: " <+> prettyTCM fieldVal
  TelV tel ty <- telView fieldVal
  lift . reportSDoc "rp" 10 $ text "ignoring tel for now: " <+> prettyTCM tel
  lift . reportSDoc "rp" 10 $ text "property: " <+> prettyTCM ty
  decTy <- decify ty
  lift . reportSDoc "rp" 10 $ text "decify property: " <+> prettyTCM decTy
  decExp <- lift $ findInstance' decTy >>= \case
    Nothing -> agda2hsErrorM $ "No Dec instance found for" <+> prettyTCM decTy
    Just decInst -> do 
      reportSDoc "rp" 10 $ text "decinst: " <+> prettyTCM decInst
      compileTerm decTy decInst
  let prop_name = Hs.Ident () . ("prop_" ++) . haskellifyName . nameNameParts . nameCanonical . qnameName $ f
  pure $
    Hs.FunBind
      ()
      [ Hs.Match
          ()
          prop_name
          []
          (Hs.UnGuardedRhs () decExp)
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
