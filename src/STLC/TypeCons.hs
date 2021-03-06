module STLC.TypeCons where
import Prelude as P
import Data.Set as S
import Data.Map as M
-- Church style typing: Types are part of the term
-- Curry style typing: Terms are UTLC, Types are "checked"

-- Note: without base types, STLC is uninhabited
data Type =
     Unit
    | Boolean
    | Prod Type Type
    | Record [(String, Type)]
    | CProd Type Type
    | Arr Type Type  -- right associative
      deriving (Show, Eq, Ord) --naive type equality(strict representation)

-- STLC + Boolean + Unit + Product type + Coproduct type + Records + Variants + recursive types
-- product types --generalize--> records a.k.a. labeled nested products
-- coproduct types --generalize--> variants a.k.a. labeled nexted coproducts
data Term = 
    -- UNITS
     U
    -- Boolean terms
    | Tru
    | Fls
    -- Product introduction
    | TmProd Term Term
    -- Product elimination
    | Pi_1 Term Type
    | Pi_2 Term Type
    -- Record introduction
    | RI [(String,Term)] -- No condition on welformed, distinct naming (shadowed)
    -- Record elimination
    | RE Term String
    -- Coproduct introduction
    | Inj_1 Term Type
    | Inj_2 Term Type
    -- Coproduct elimination
    | Match Term Term Term
    -- STLC
    | TmVar Int
    | TmAbs Type Term
    | TmApp Term Term
      deriving (Show, Eq, Ord) --naive term equality(strict representation)

-- Not enforcing substructural rules like 
-- Weakening, exchange, ...etc
type Ctxt = Set (Term, Type)

isVal :: Term -> Bool
isVal (TmAbs _ _) = True
-- Records are values
isVal (RI _) = True
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

-------------------
Gamma |- Tru : Boolean
 -}
typeCheck ctx Tru Boolean = True
{-

-------------------
Gamma |- Fls : Boolean
 -}
typeCheck ctx Fls Boolean = True

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

-- Extensions
{- 
Gamma |- t1 : T1  Gamma |- t2 : T2
------------------------------------
Gamma |- TmProd t1 t2 : Prod T1 T2
-}
typeCheck ctx (TmProd t1 t2) (Prod ty1 ty2) = let r1 = typeCheck ctx t1 ty1
                                                  r2 = typeCheck ctx t2 ty2
                                                in r1 && r2
{- 
Gamma |- p : Prod T1 T2
-------------------------------
Gamma |- Pi_1 p T2 : T1
-}                                              
typeCheck ctx (Pi_1 p ty2) ty1 = typeCheck ctx p (Prod ty1 ty2)
{- 
Gamma |- p : Prod T1 T2
-------------------------------
Gamma |- Pi_2 p T1 : T2
-}                                              
typeCheck ctx (Pi_2 p ty1) ty2 = typeCheck ctx p (Prod ty1 ty2)
{-
Gamma |- t1 : T1 ... Gamma |- tn : Tn
---------------------------------------------------------------------
Gamma |- RI [(s1, t1), (s2, t2)... (sn, tn)] : [(s1, T1)...(sn, Tn)]
-}
typeCheck ctx (RI terms) (Record types) = check terms types where
                                 check ((s1,trm):[]) ((s2,typ):[]) | s1 == s2 = typeCheck ctx trm typ
                                 check ((s1,trm):trms) ((s2,typ):typs)| s1 == s2 = typeCheck ctx trm typ && check trms typs
{- 
(si,ti) in record    Gamma |- ti : Ti
--------------------------------------
Gamma |- RE record si : Ti 
-}
typeCheck ctx (RE (RI record) si) typi = maybe False (\r -> typeCheck ctx r typi) (find si record) where
                                            find s [] = Nothing
                                            find s ((s1,trm):trms) | s == s1 = Just trm
                                            find s ((s1,trm):trms) | s /= s1 = find s trms
                                            

{- 
Gamma |- t : T1
-------------------------------
Gamma |- Inj_1 t T2 : T1 + T2
-}
typeCheck ctx (Inj_1 t ty2) (CProd ty1 ty2') | ty2 == ty2' = typeCheck ctx t ty1
{- 
Gamma |- t : T2
--------------------------------
Gamma |- Inj_2 t T1 : T1 + T2
-}
typeCheck ctx (Inj_2 t ty1) (CProd ty1' ty2) | ty1 == ty1' = typeCheck ctx t ty2
{- 
Gamma |- t1 : T1 -> T3   Gamma |- t2 : T2 -> T3  Gamma |- c : T1 + T2
----------------------------------------------------------------------
Gamma |- Match c t1 t2 : T3
-}
typeCheck ctx (Match c (TmAbs ty1 b1) (TmAbs ty2 b2)) ty3 = let r1 = typeCheck ctx (TmAbs ty1 b1) (Arr ty1 ty3)
                                                                r2 = typeCheck ctx (TmAbs ty2 b2) (Arr ty1 ty3)
                                                                r3 = typeCheck ctx c (CProd ty1 ty2)
                                                            in r1 && r2 && r2
  
  

typeCheck _ _ _ = False

-- Properties: Decidable typing, uniqueness of typing, Preservation, Progress

type Typing = Map Term Type
getType' :: Typing -> Term -> Maybe Type
getType' ctxt U = Just Unit
getType' ctxt Tru = Just Boolean
getType' ctxt Fls = Just Boolean
getType' ctxt (TmVar n) = M.lookup (TmVar n) ctxt
getType' ctxt (TmAbs ty1 b) = getType' (M.insert (TmVar $ M.size ctxt) ty1 ctxt) b  >>= \ ty2 -> Just $ Arr ty1 ty2
getType' ctxt (TmApp t1 t2) = do
                                ty12' <- getType' ctxt t1
                                ty1' <- getType' ctxt t2
                                r <- case ty12' of
                                      (Arr ty1 ty2) | ty1 == ty1' -> Just ty2
                                      _ -> Nothing 
                                return r
getType' ctxt (TmProd t1 t2) = do
                                  ty1 <- getType' ctxt t1
                                  ty2 <- getType' ctxt t2
                                  return $ Prod ty1 ty2
getType' ctxt (Pi_1 p ty2) = do
                                ty12 <- getType' ctxt p
                                r <- case ty12 of
                                  (Prod ty1 ty2) -> Just ty1
                                return r
getType' ctxt (Pi_2 p ty1) = do
                                ty12 <- getType' ctxt p
                                r <- case ty12 of
                                  (Prod ty1 ty2) -> Just ty2
                                return r 

getType' ctxt (RI terms) = (sequence $ P.map (\(s,t) -> (getType' ctxt t) >>= (\ty -> Just (s,ty))) terms) >>= (\r -> Just $ Record r)
getType' ctxt (RE record s) = do
                                tyrec <- getType' ctxt record 
                                r <- case tyrec of 
                                  (Record typs) -> find s typs where
                                                   find s [] = Nothing
                                                   find s ((s',ty):xs)| s' == s = Just ty
                                                   fins s ((s',ty):xs) = find s xs
                                return r
getType' ctxt (Inj_1 c ty2) = do 
                                ty1 <- getType' ctxt c
                                return $ CProd ty1 ty2                                                           
getType' ctxt (Inj_2 c ty1) = do 
                                ty2 <- getType' ctxt c
                                return $ CProd ty1 ty2
getType' ctxt (Match c t1 t2) = do
                                  tyc <- getType' ctxt c    
                                  ty13 <- getType' ctxt t1
                                  ty23 <- getType' ctxt t2     
                                  r <- case (tyc,ty13,ty23) of
                                    (CProd ty1 ty2, Arr ty1' ty3, Arr ty2' ty3')| ty1 == ty1' && ty2 == ty2' && ty3 == ty3' -> Just ty3
                                  return r                     

getType :: Term -> Maybe Type
getType = getType' M.empty


tru :: Term
tru = TmAbs Unit $ TmAbs Unit $ TmVar 1

fls :: Term
fls = TmAbs Unit $ TmAbs Unit $ TmVar 0

p :: Term
p = TmProd tru fls

-- flat Bool valued tree (non recursive)
booltree :: Type
booltree  = CProd (Unit) (Prod (Prod Unit Boolean) Unit)

leaf :: Term
leaf = Inj_1 U (Prod (Prod Unit Boolean) Unit)

node :: Term
node = Inj_2 (TmProd (TmProd U Tru) U) Unit

test1 :: Bool
test1 = typeCheck S.empty leaf booltree == True
test2 :: Bool
test2 = typeCheck S.empty node booltree == True

-- 0 ~ Fls, 1 ~ Tru
height :: Term
height = Match node (TmAbs Unit Fls) (TmAbs (Prod (Prod Unit Boolean) Unit) Tru)

-- Add variants?
-- recursive types , (equirecursive or isorecursive types?)
-- https://www.cs.purdue.edu/homes/suresh/565-Spring2009/lectures/lecture-17.pdf