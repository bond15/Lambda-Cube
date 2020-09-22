module STLC.DeBruijn where
import Data.Set as S
import Data.Map as M
-- Church style typing: Types are part of the term
-- Curry style typing: Terms are UTLC, Types are "checked"

-- Note: without base types, STLC is uninhabited
data Type =
      Unit 
    | Arr Type Type  -- right associative
      deriving (Show, Eq, Ord) --naive type equality(strict representation)

data Term = 
      TmVar Int
    | TmAbs Type Term
    | TmApp Term Term
    | U deriving (Show, Eq, Ord) --naive term equality(strict representation)

-- Not enforcing substructural rules like 
-- Weakening, exchange, ...etc
type Ctxt = Set (Term, Type)

isVal :: Term -> Bool
isVal (TmAbs _ _) = True
isVal _ = False

-- alternative, define a getType operation instead of a check operation
-- infer vs check , idea behind bidirectional type checking?
typeCheck :: Ctxt -> Term -> Type -> Bool
{- 

-------------------
 Gamma |-  T : Unit
-}
typeCheck ctx U Unit = True

{- 
  x : T in Gamma
-------------------
 Gamma |- x : T
-}
typeCheck ctx (TmVar n) ty = S.member ((TmVar n), ty) ctx

{-
Gamma, x : T1 |- t2 : T2
-------------------------------
Gamma |- \x : T1. t2 : T1 -> T2
-}
typeCheck ctx (TmAbs ty1 t2) (Arr ty1' ty2) | ty1 == ty1' = typeCheck (S.insert (TmVar (S.size ctx),ty1) ctx) t2 ty2
typeCheck ctx (TmAbs ty1 t2) (Arr ty1' ty2) | ty1 /= ty1' = False

{--
Gamma |- t1 : T1 -> T2    Gamma |- t2 : T1
-------------------------------------------
Gamma |- t1 t2 : T2
-}
-- have to peek at t1 here, must be a lambda abstraction
typeCheck ctx (TmApp (TmAbs ty1 b) t2) ty2 = let r1 = typeCheck ctx (TmAbs ty1 b) (Arr ty1 ty2) 
                                                 r2 = typeCheck ctx t2 ty1
                                              in r1 && r2

typeCheck _ _ _ = False

-- Properties: Decidable typing, uniqueness of typing, Preservation, Progress

type Typing = Map Term Type
getType' :: Typing -> Term -> Maybe Type
getType' ctxt U = Just Unit
getType' ctxt (TmVar n) = M.lookup (TmVar n) ctxt
getType' ctxt (TmAbs ty1 b) = getType' (M.insert (TmVar $ M.size ctxt) ty1 ctxt) b  >>= \ ty2 -> Just $ Arr ty1 ty2
getType' ctxt (TmApp t1 t2) = do
                                ty12' <- getType' ctxt t1
                                ty1' <- getType' ctxt t2
                                r <- case ty12' of
                                      (Arr ty1 ty2) | ty1 == ty1' -> Just ty2
                                      _ -> Nothing 
                                return r
getType :: Term -> Maybe Type
getType = getType' M.empty


tru :: Term
tru = TmAbs Unit $ TmAbs Unit $ TmVar 1

fls :: Term
fls = TmAbs Unit $ TmAbs Unit $ TmVar 0
