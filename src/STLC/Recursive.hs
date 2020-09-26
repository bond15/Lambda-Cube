module STLC.Recursive where

import Data.Set as S
import Data.Map as M
-- Church style typing: Types are part of the term
-- Curry style typing: Terms are UTLC, Types are "checked"

-- Note: without base types, STLC is uninhabited
data Type =
      Unit
    | TyVarX -- generalize, multiple variables
    | MuX Type 
    | Arr Type Type  -- right associative
      deriving (Show, Eq, Ord) --naive type equality(strict representation)

data Term = 
      U
    | TmVar Int
    | TmAbs Type Term
    | TmApp Term Term
    | Fold Type Term
    | Unfold Type Term
      deriving (Show, Eq, Ord) --naive term equality(strict representation)

tySub :: Type -> Type-> Type
tySub Unit u = Unit
tySub TyVarX u = u
tySub (MuX t) u = MuX $ tySub t u
tySub (Arr t1 t2) u = Arr (tySub t1 u) (tySub t2 u)

-- Not enforcing substructural rules like 
-- Weakening, exchange, ...etc
type Ctxt = Set (Term, Type)

isVal :: Term -> Bool
isVal (TmAbs _ _) = True
isVal (Fold _ _ ) = True
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
{- 
U = Mu.X T1    Gamma |- t1 : [X -> U] T1
-----------------------------------------
Gamma |- Fold U t1 : U
-}
typeCheck ctx (Fold (MuX ty1) t1) u = typeCheck ctx t1 (tySub ty1 u)
--                                  
{-
U = Mu X T1   Gamma |- t1 : T1
-----------------------------------------
Gamma |- Unfold U t1 : [X -> U] T1
 -}
typeCheck ctx (Unfold (MuX ty1) t1) r = let r1 = typeCheck ctx t1 ty1
                                            r2 = r == tySub ty1 (MuX ty1)
                                         in r1 && r2
{-

Mu X = A + (B x X)

U = Mu (A + (B x TyvarX))   Gamma |- (Inj_1 a (B x TyVarX)) : Mu (A + (B x Mu (A + (B x TyvarX))))
-------------------------------------------------------------------------------
nil = fold [Mu (A + (B x TyVarX))] (Inj_1 a (B x TyVarX)) : Mu A + (B x TyVarX)

cons = \b : B -> \x : ? -> fold ? Inj_2 (b , x)

-}

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