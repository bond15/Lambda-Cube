module UTLC.DeBruijn where

{-
De Bruijn Indecies
the `Named` representaiton implemented in Named.hs only allows closed terms

You can represent open terms if there is a global context 

De Bruijn indecies remove the need for "alpha equivalence" buy using Nats to represent which binder a var belongs to.
If the term is open, there is a context containing vars and their indecies.

ex - closed terms
\x. \y. \z. x y z  =  \.\.\.2 1 0
\x.\y.x (y x) = \.\.1 (0 1) 

Indecies are counted from right -> left

ex - open terms
Gamma := z -> 2, y -> 1, x -> 0
(x (y z)) = (0 (1 2))

ex - mixed, open term with binder
Gamma := z -> 2, y -> 1, x -> 0 ==> (shift) Gamma' := z -> 3, y -> 2, x -> 1, p -> 0
\p. x p  = \.1 0

Gamma := z -> 2, y -> 1, x -> 0  ==> (shift) Gamma':= z -> 4, y -> 3, x -> 2, p -> 1, q -> 0
\p.\q. y p q = \.\. 3 1 0

-- think kind of like a context stack


-- Set of Terms := Family of Sets indexed by Nat where Sn for n in Nat is the set of terms with at most n free variables

To specify an exact term, 
    - must specify what Tn set it lives in (how many free variables it can have)
    - a naming context for the free variables

t in Tn with Gamma (where n is the length of Gamma)

-}

data Term = 
      TmVar Int
    | TmAbs Term
    | TmApp Term Term deriving Show

-- d shift of a term t, above cuttoff c
shift :: Int -> Int -> Term -> Term
shift c d (TmVar k) | k < c = (TmVar k)
shift c d (TmVar k) | k >= c = (TmVar $ k + d)
shift c d (TmAbs t) = (TmAbs $ shift (c + 1) d t)
shift c d (TmApp t1 t2) = (TmApp (shift c d t1) (shift c d t2))

-- shift free variables by d, c keeps count of how many lambdas in a term (don't shift those since they are bound)
-- ex
{- shift 2 ==> 0 2
{c = 0, d = 2} \.\. 1 (0 2)
\. {c = 1, d = 2} \.1 (0 2)
\.\. {c = 2, d =  2} 1 (0 2)
===>*
\.\. 1 (0 4)
-}
-- total function w/o renaming
subst :: Int -> Term -> Term -> Term
subst j s (TmVar k) | k == j = s
subst j s (TmVar k) | k /= j = TmVar k
subst j s (TmAbs t) = TmAbs $ subst (j+1) (shift 0 1 s) t 
subst j s (TmApp t1 t2) = TmApp (subst j s t1) (subst j s t2)

isVal :: Term -> Bool
isVal (TmAbs _) = True
isVal _ = False

eval :: Term -> Term
-- eval_Beta
--eval (TmApp (TmAbs x t) v) | isVal v = subst x v t
eval (TmApp (TmAbs t) v) | isVal v = shift 0 (-1) (subst 0 (shift 0 1 v) t)
    -- increse context by 1(in lambda)
    -- substitute
    -- decrese context by 1(removed lambda)
-- eval_App_2
eval (TmApp v t) | isVal v = (TmApp v (eval t))
-- eval_App_1
eval (TmApp t1 t2) = (TmApp (eval t1) t2)
-- done
eval v | isVal v = v


id' :: Term
id' = TmAbs $ TmVar 0

tru :: Term
tru = TmAbs $ TmAbs $ TmVar 1

fls :: Term
fls = TmAbs $ TmAbs $ TmVar 0

constT :: Int -> Term
constT n = TmAbs $ TmVar n

ex1 :: Term
ex1 = TmApp (TmApp tru (constT 4)) (constT 7)