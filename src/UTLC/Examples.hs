module UTLC.Examples where

import UTLC.Named
import UTLC.Eval

constT :: String -> Term
constT s = TmAbs s $ TmVar s

id' :: Term
id' = TmAbs "x" $ TmVar "x"

tru :: Term
tru = TmAbs "x" $ TmAbs "y" $ TmVar "x"

fls :: Term
fls = TmAbs "x" $ TmAbs "y" $ TmVar "y"

cond :: Term -- \c -> \b1 -> \b2 -> c b1 b2
cond = TmAbs "c" $ TmAbs "b1" $ TmAbs "b2" $ TmApp (TmApp (TmVar "c") (TmVar "b1")) (TmVar "b2")

omega :: Term
omega = TmApp (TmAbs "x" $ TmApp (TmVar "x") (TmVar "x")) (TmAbs "x" $ TmApp (TmVar "x") (TmVar "x"))

ex :: Term
ex = TmApp id' $ constT "z"

ex2 :: Term
ex2 = TmApp (TmApp tru (constT "p")) (constT "q") -- ==> (constT "p")

ex3 :: Term -- if true then p else q ==> p
ex3 = TmApp (TmApp (TmApp cond tru) (constT "p")) (constT "q")

ex4 :: Bool -- ==> eval (omega) ==> omega
ex4 = eval omega == omega
