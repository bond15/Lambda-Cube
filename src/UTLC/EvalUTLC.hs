module UTLC.EvalUTLC where

import UTLC.NamedUTLC (Term(TmApp, TmVar, TmAbs), subst)

-- Operational semantics
-- values are a subset of terms
-- at the end of a reduction
-- Values = (TmApp var t)
isVal :: Term -> Bool
isVal (TmAbs _ _) = True
isVal _ = False
-- alternatively TmAbs is a value only when its body is evaulated fully


-- Different evaluation strategies (Same terms + same substitution rule?)
-- Call by name 
-- Call by value
-- Call by need lazy eval

-- "one step" evaluation relation
eval :: Term -> Term
-- eval_Beta
eval (TmApp (TmAbs x t) v) | isVal v = subst x v t
-- eval_App_2
eval (TmApp v t) | isVal v = (TmApp v (eval t))
-- eval_App_1
eval (TmApp t1 t2) = (TmApp (eval t1) t2)

