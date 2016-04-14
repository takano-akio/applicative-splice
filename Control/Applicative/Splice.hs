{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DisambiguateRecordFields #-}

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
module Control.Applicative.Splice
  ( appl
  ) where

import Control.Monad.Trans.State
import Data.Foldable
import Data.Generics
import qualified Data.Sequence as Q
import Language.Haskell.Exts
import qualified Language.Haskell.Meta as Meta
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH

data ApplicativeExp exp
  = Pure exp
  | Ap (ApplicativeExp exp) exp
  deriving (Functor)

-- | The applicative-splice quasiquoter.
appl :: TH.QuasiQuoter
appl = TH.QuasiQuoter
  { quoteExp = foo
  , quotePat = err
  , quoteType = err
  , quoteDec = err
  }
  where
    err _ = fail "This quasiquoter can only used in an expression"

quote :: Exp -> ApplicativeExp Exp
quote e0 = foldl' Ap (Pure fun) splices
  where
    fun = foldr mkLam body $ map argVar $ zipWith const [0..] $ toList splices
    mkLam var e = Lambda uninformativeSrcloc [PVar var] e

    (body, splices) = runState go Q.empty

    go = everywhereM' (mkM onSplice) e0

    onSplice (SpliceExp splice) = do
      list <- get
      let !n = length list
      put $ list Q.|> e
      return $ Var $ UnQual $ argVar n
      where
        !e = case splice of
          IdSplice str -> Var $ UnQual $ Ident str
          ParenSplice x -> x
    onSplice e = return e

argVar :: Int -> Name
argVar = Ident . ("applicative_splice_" ++) . show

foo :: String -> TH.ExpQ
foo str = do
  e <- case parseExpWithMode parseMode str of
    ParseOk e -> return e
    ParseFailed loc msg -> fail $ show loc ++ ": " ++ msg
  unApplicative $ Meta.toExp <$> quote e
  where
    parseMode = defaultParseMode
      { extensions = map EnableExtension [TemplateHaskell]
      }

unApplicative :: ApplicativeExp TH.Exp -> TH.ExpQ
unApplicative (Pure e) = [| pure $(pure e) |]
unApplicative (Ap (Pure f) a) = [| $(pure f) <$> $(pure a) |]
unApplicative (Ap f a) = [| $(unApplicative f) <*> $(pure a) |]

everywhereM' :: (Monad m) => GenericM m -> GenericM m
everywhereM' f x = do 
  x' <- f x
  gmapM (everywhereM' f) x'

uninformativeSrcloc :: SrcLoc
uninformativeSrcloc = SrcLoc
  { srcFilename = "<none>"
  , srcLine = 0
  , srcColumn = 0
  }

view :: TH.ExpQ -> TH.ExpQ
view eq = do
  e <- eq
  let str = TH.pprint e
  [| putStrLn str |]
