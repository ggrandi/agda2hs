{-# OPTIONS_GHC -W #-}

module Agda2Hs.Compile.Laws (compileLaws) where

import Agda.Compiler.Backend

import Agda.Syntax.Common hiding (Ranged)
import Agda.Syntax.Internal hiding (QName)

import Agda.TypeChecking.Pretty
import Agda.Utils.Lens
import Agda.Utils.ListT
import Agda.Utils.Monad (lift)

import Agda2Hs.Compile.Types

import qualified Agda2Hs.Language.Haskell as Hs
import Control.Applicative
import Control.Monad
import Data.Bifunctor

fromFoldable :: (Foldable f, Monad m) => f a -> ListT m a
fromFoldable = foldr consListT nilListT

-- fromFoldable' :: (Foldable f, Monad m) => m (f a) -> ListT m a
-- fromFoldable' = lift >=> fromFoldable

haskellifyName :: ArgName -> ArgName
haskellifyName =
  foldr
    ( \case
        '-' -> ('_' :)
        x -> (x :)
    )
    []

telToProperties :: Telescope -> ListT C (ArgName, Type)
telToProperties x = do
  x <- fromFoldable . telToList $ x
  unless ((argInfoHiding . domInfo $ x) == NotHidden) empty
  pure . first haskellifyName . unDom $ x

-- getConstInfo
compileLaws :: Definition -> C [Hs.Decl ()]
compileLaws def = sequenceListT $ do
  lift . reportSDoc "rp" 10 $ text "name: " <+> (pretty . defType $ def)
  lift . reportSDoc "rp" 10 . pshow . defType $ def
  x <- case unEl . defType $ def of
    Def q _elims -> pure q
    x -> do
      lift . reportSDoc "rp" 10 $ text "expected def but got: " <+> pretty x
      empty
  lift . reportSDoc "rp" 10 $ pretty x
  (name, _ty) <-
    (getConstInfo x <&> theDef) >>= \case
      RecordDefn x -> telToProperties . _recTel $ x
      _ -> do
        lift . reportSDoc "rp" 10 $ text "expected RecordDefN but got: " <+> pretty x
        empty
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
