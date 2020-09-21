module STLC.DeBruijn where

-- Church style typing: Types are part of the term
-- Curry style typing: Terms are UTLC, Types are "checked"

data Type =
      Unit 
    | Bool
    | Arr Type Type  -- right associative
      deriving (Show)

data Term = 
      TmVar Int
    | TmAbs Type Term
    | TmApp Term Term
    | T
    | True
    | False

