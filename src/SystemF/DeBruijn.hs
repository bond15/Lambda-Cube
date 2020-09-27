module SystemF.DeBruijn where
import Data.Set as S
import Data.Map as M



data Type =
    -- base types
      Unit 
    -- STLC
    | Arr Type Type  -- right associative
    -- Polymorphism
    | TyVar String
    | Poly Type Type
      deriving (Show, Eq, Ord) --naive type equality(strict representation)

data Term = 
    -- base types
      U
    -- STLC
    | TmVar Int
    | TmAbs Type Term
    | TmApp Term Term
    -- Polymorphism
    | TmTAbs Type Term
    | TmTApp Term Type
      deriving (Show, Eq, Ord) --naive term equality(strict representation)



--[X -> T]T2 
-- TODO capture avoiding
tySub :: Type -> Type -> Type -> Type
tySub (TyVar x) t t2 = case t2 of
                            (Arr ty1 ty2) -> (Arr (tySub (TyVar x) t ty1) (tySub (TyVar x) t ty2))
                            (TyVar n) | (TyVar n) == (TyVar x) -> t
                            (TyVar n) | (TyVar n) /= (TyVar x) -> (TyVar n)
                            (Poly (TyVar y) body) -> (Poly (TyVar y) (tySub (TyVar x) t body))

-- Not enforcing substructural rules like 
-- Weakening, exchange, ...etc
data Ctxt = Ctxt {terms :: Set (Term, Type), types :: Set(Type)}

insertTerm :: (Term, Type) -> Ctxt-> Ctxt
insertTerm (t,ty) ctx = ctx { terms = S.insert (t,ty) (terms ctx)}

insertType :: Type -> Ctxt -> Ctxt
insertType x ctx = ctx { types = S.insert x (types ctx)}

ctxtSize :: Ctxt -> Int
ctxtSize ctx = S.size $ terms ctx

hasTerm :: Ctxt -> (Term,Type) -> Bool
hasTerm ctxt t = S.member t $ terms ctxt


isVal :: Term -> Bool
isVal (TmAbs _ _) = True
isVal (TmTAbs _ _) = True
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
typeCheck ctx (TmVar n) ty = hasTerm ctx ((TmVar n), ty)

{-
Gamma, x : T1 |- t2 : T2
-------------------------------
Gamma |- \x : T1. t2 : T1 -> T2
-}
typeCheck ctx (TmAbs ty1 t2) (Arr ty1' ty2) | ty1 == ty1' = typeCheck (insertTerm (TmVar (ctxtSize ctx),ty1) ctx) t2 ty2
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


--EXTENSION - Polymorphism
{-
Gamma, X |- t : ty
-------------------------------------T-TyAbs
Gamma |- TmTAbs "X" t : (Poly (TyVar X) ty) 
-}
typeCheck ctx (TmTAbs (TyVar x) t ) (Poly (TyVar x') ty) = let r1 = x == x'
                                                               r2 = typeCheck (insertType (TyVar x) ctx) t ty
                                                           in r1 && r2
{-
Gamma |- t : (Poly X ty2)
-------------------------------------T-TyApp
Gamma |- t [ty1] : [X -> ty1] ty2
-}
 -- need to know X...



typeCheck _ _ _ = False

data Typing = Typing {terms' :: Map Term Type, types' :: Set(Type)}
tyLookup :: Typing -> Term -> Maybe Type
tyLookup typing t = M.lookup t $ terms' typing 

tyInsert :: Typing -> Type -> Typing
tyInsert typing ty = typing { types' = S.insert ty (types' typing)}

tmInsert :: Typing -> Term  -> Type -> Typing
tmInsert typing t ty = typing { terms' = M.insert t ty (terms' typing) }

tmSize :: Typing -> Int
tmSize typing = M.size $ terms' typing

getType' :: Typing -> Term -> Maybe Type
getType' ctxt U = Just Unit
getType' ctxt (TmVar n) = tyLookup ctxt (TmVar n) 
getType' ctxt (TmAbs ty1 b) = getType' (tmInsert ctxt (TmVar $ tmSize ctxt) ty1) b  >>= \ ty2 -> Just $ Arr ty1 ty2
getType' ctxt (TmApp t1 t2) = do
                                ty12' <- getType' ctxt t1
                                ty1' <- getType' ctxt t2
                                r <- case ty12' of
                                      (Arr ty1 ty2) | ty1 == ty1' -> Just ty2
                                      _ -> Nothing 
                                return r
getType' ctxt (TmTAbs (TyVar x) t) = do 
                                       ty <- getType' (tyInsert ctxt (TyVar x)) t
                                       return $ Poly (TyVar x) ty
getType' ctxt (TmTApp t ty) = do
                                r1 <- getType' ctxt t
                                r2 <- case r1 of 
                                        (Poly (TyVar x) ty2) -> Just $ tySub (TyVar x) ty ty2
                                        _ -> Nothing
                                return r2

getType' ctx _ = Nothing

getType :: Term -> Maybe Type
getType = getType' $ Typing { terms' = M.empty, types' = S.empty}


tru :: Term
tru = TmAbs Unit $ TmAbs Unit $ TmVar 1

fls :: Term
fls = TmAbs Unit $ TmAbs Unit $ TmVar 0

-- identity
ex_id = (TmAbs Unit (TmVar 0))
-- Just (Arr Unit Unit)
-- polymorphic identity
ex_pid = (TmTAbs (TyVar "X") (TmAbs (TyVar "X") (TmVar 0))) 
--Just (Poly (TyVar "X") (Arr (TyVar "X") (TyVar "X")))

ex_app = (TmTApp ex_pid Unit)
-- Just (Arr Unit Unit)
-- \A -> \B -> \f : A -> B -> \a : A -> f a
apply = TmTAbs (TyVar "A") 
            (TmTAbs (TyVar "B") 
                (TmAbs (Arr (TyVar "A") (TyVar "B")) 
                    (TmAbs (TyVar "A") 
                        (TmApp (TmVar 1) (TmVar 0)))))
