module UTLC.Named(
  Term(..), -- exports all constructors for this type
  subst
) where
import Data.Set (Set, union, insert, delete, empty, notMember)

-- Software foundations
-- https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html

type Var = String

data Term = 
      TmVar Var
    | TmAbs Var Term
    | TmApp Term Term deriving (Show, Eq) -- naive non alpha equivalent EQ instance

-- Terminology (Open := when a term has free variables, closed := when a term has no free variables)
freeVars :: Set Var -> Term -> Set Var
freeVars s (TmVar var) = insert var s
freeVars s (TmAbs var t) = delete var $ freeVars s t
freeVars s (TmApp t1 t2) = (freeVars s t1) `union` (freeVars s t2)

-- using pattern gaurds for capture avoiding conditions
subst :: Var -> Term -> Term -> Term
subst var s (TmVar x) | var == x = s
subst var s (TmVar x) | var /= x = (TmVar x)
subst var s (TmAbs y t) | var /= y && (notMember y $ freeVars empty s) = (TmAbs y (subst var s t)) -- capture avoiding substitution
subst var s (TmApp t1 t2) = (TmApp (subst var s t1) (subst var s t2))
subst _ _ _ = undefined -- need renaming (in TmAbs case) to make this a total function
