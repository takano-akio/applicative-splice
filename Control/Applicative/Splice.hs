{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | This module defines a quasiquoter for making it easier to program with
-- applicatives and monads.
--
-- = Basic usage
--
-- The 'appl' quasiquoter takes almost any Haskell expression, and expands to the
-- same Haskell expression, wrapped in a call to 'pure'. For example,
--
-- @
--   [appl| 4 + 5 |]
--      -- expands to:
--      pure (4 + 5)
-- @
--
-- Additionally, the expression given to 'appl' may contain "splices". A splice
-- is a dollar sign immediately followed by a parenthesized expression.
-- The parentheses can be dropped if the expression consists of a single
-- identifier. Here are examples of splices.
--
-- @
--   $(f a b)
--   $([0..7])
--   $getLine
-- @
--
-- The syntax for splices are stolen from Template Haskell
-- splices. Therefore whitespaces are not allowed after the dollar sign.
--
-- The expression inside a splice should have the type @f a@ for some
-- 'Applicative' @f@ and some type @a@. The splice itself should be
-- placed in a context where a value of type @a@ is expected. Then 'appl' expands
-- to an applicative expression that "embeds" the result of the applicative
-- action in the pure context. For example,
--
-- @
--   [appl| f $x (4 + $y) |]
--      -- expands to:
--      (\\a b -> f a (4 + b)) \<$> x \<*> y
-- @
--
-- In terms of types, the dollar sign is like a function of type @forall a. f a -> a@,
-- although it is not a real function.
--
-- The type of the 'appl' expression will be in the same applicative as the
-- splices. This also means mutliple splices in the same block must
-- share the same applicative.
--
-- = Special case: functor splices
--
-- When an 'appl' block contains exactly one splice, the type of the expression
-- inside the splice can be @f a@ for any functor @f@, and it doesn't have to be
-- an applicative. The expansion will only contain a call to '<$>', not 'pure'
-- or '<*>'.
--
-- @
--   [appl| (\"Length\", length $m) |]
--      -- expands to:
--      (\\a -> (\"Length\", length a)) \<$> m
-- @
--
-- = Nested splices for monads
--
-- When your applicative is also a monad, you can have splices inside another
-- splice. For example,
--
-- @
--   [appl| $(putStrLn $ "Hello, " ++ $getLine) |]
--      -- expands to:
--      getLine >>= (\\a -> putStrLn $ "Hello, " ++ a)
-- @
--
-- As in this case, no call to '<$>' is generated if the whole 'appl' block
-- consists of a single splice.
module Control.Applicative.Splice
  ( appl
  ) where

import Control.Monad.State
import Control.Monad.Writer
import Data.Generics
import qualified Language.Haskell.Exts as H
import qualified Language.Haskell.Meta as Meta
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH

data ApplicativeExp var exp
  = AdoJoin [(var, ApplicativeExp var exp)] exp
  -- ado { v0 <- join e0; v1 <- join e1; ...; return eN }
  deriving (Functor)

-- | The applicative-splice quasiquoter.
appl :: TH.QuasiQuoter
appl = TH.QuasiQuoter
  { quoteExp = genExp
  , quotePat = err
  , quoteType = err
  , quoteDec = err
  }
  where
    err _ = fail "This quasiquoter can only be used in an expression"

genExp :: String -> TH.ExpQ
genExp str = do
  e <- case H.parseExpWithMode parseMode str of
    H.ParseOk e -> return e
    H.ParseFailed loc msg -> fail $ show loc ++ ": " ++ msg
  unApplicative $ bimapApplicativeExp Meta.toName Meta.toExp $ quote e
  where
    parseMode = H.defaultParseMode
      { H.extensions = map H.EnableExtension [H.TemplateHaskell]
      }

bimapApplicativeExp
    :: (a -> c)
    -> (b -> d)
    -> ApplicativeExp a b
    -> ApplicativeExp c d
bimapApplicativeExp f g = go
  where
    go (AdoJoin binds body) = AdoJoin (map goBind binds) (g body)
    goBind (var, app) = (f var, go app)

quote :: H.Exp -> ApplicativeExp H.Name H.Exp
quote e0 = evalState (go e0) 0
  where
    go e = do
      (body, binds) <- runWriterT (everywhereM' (mkM onSplice) e)
      return $ AdoJoin binds body

    onSplice (H.SpliceExp splice) = do
      v <- gensym
      e' <- lift $ go e
      tell [(v, e')]
      return $ H.Var $ H.UnQual v
      where
        !e = case splice of
          H.IdSplice str -> H.Var $ H.UnQual $ H.Ident str
          H.ParenSplice x -> x
    onSplice e = return e

    gensym = do
      n <- get
      put $! n + 1
      return $ argVar n

argVar :: Int -> H.Name
argVar = H.Ident . ("applicative_splice_" ++) . show

unApplicative :: ApplicativeExp TH.Name TH.Exp -> TH.ExpQ
unApplicative (AdoJoin (unzip -> (vars, args)) body) = case args of
  [] -> [| pure $(pure body) |]
  first:rest -> foldl mkAp (join $ mkFmap <$> fun <*> unJoin first) rest
  where
    fun = TH.lamE (map TH.varP vars) (pure body)
    mkAp f a = [| $f <*> $(unJoin a) |]
    mkFmap f a
      | isTrivialIdentity f = pure a
      | otherwise = [| $(pure f) <$> $(pure a) |]
    isTrivialIdentity (TH.LamE [TH.VarP v] e) = e == TH.VarE v
    isTrivialIdentity _ = False

unJoin :: ApplicativeExp TH.Name TH.Exp -> TH.ExpQ
unJoin (AdoJoin binds body) = foldr bind (pure body) binds
  where
    bind (v, a) b = [| $(unJoin a) >>= \ $(TH.varP v) -> $b |]

everywhereM' :: (Monad m) => GenericM m -> GenericM m
everywhereM' f x = do 
  x' <- f x
  gmapM (everywhereM' f) x'

view :: TH.ExpQ -> TH.ExpQ
view eq = do
  e <- eq
  let str = TH.pprint e
  [| putStrLn str |]
