module DTT.DTT where
import Control.Monad ( unless )
import Control.Monad.Except (throwError)

-- https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf
-- Reding STLC based on this presentation, then extending with dependent types

{- Notably, this uses Bidirectional type checking
  https://arxiv.org/pdf/1908.05839.pdf

  The typical typing judgement 
    Gamma |- t : T
  is broken into 2 judgments

    Gamma |- t <- T (or down arrow)
        Under Gamma, expression t checks against type T 
        

    Gamma |- t -> T (or up arrow)
        Under Gamma, expression t synthesizes (infered) type A
        
-}

{- Design Choices:
-- Locally Nameless representation
    - locally bound variables are represented by de Bruijn indecies
    - free variables are named

        - Consequence: have to do a Quoting operation for 
        function equality since haskell functions cannot be compared
        for equality

-- Higher-order abstract syntax to represent values
    - leveraging the host language (Haskell) for substitution and values
-}

--------------------
-- ABSTRACT SYNTAX--
--------------------

{-
DTT Changes
- "Everything is a term" the term,type,kind deliniation blurs
- Thus, Evaluation is now for terms and types
- Evaluation is in type checking
-}


-- no longer require Type and Kind
data Term_up = -- (infer)
    -- previously: Ann Term_dwn Type (but now types are also terms)
      Ann Term_dwn Term_dwn 
    | Bound Int
    | Free Name
    | Term_up :@: Term_dwn
    -- new
    | Star
    | Pi Term_dwn Term_dwn
      deriving (Show, Eq)


data Term_dwn = -- (check)
      Inf Term_up -- just embeds inferable terms in checkable terms
                  -- somewhat expected as inferable subset checkable
    | Lam Term_dwn
      deriving (Show, Eq)

data Name =  -- locally nameless
      Global String
    | Local Int
    | Quote Int -- used for quoting 
      deriving (Show, Eq)



{-
 values as 
    value := n -- neutral term
            | \x ->v  -- lambda abstraction
    where
        neutral := x -- variable
                 | n v -- application
-}

data Value =
      VLam (Value -> Value) -- using host (haskell) language functions
    | VNeutral Neutral
    -- new
    | VStar
    | VPi Value (Value -> Value)

-- ex constant function
-- const x y = x -- haskell
-- const = VLam (\x -> (VLam (\y -> x))) -- STLC

data Neutral = 
      NFree Name
    | NApp Neutral Value

-- create a value for a free variable
vfree :: Name -> Value
vfree n = VNeutral (NFree n)



----------------
-- EVALUATION --
----------------

type Env = [Value]

-- infer
eval_up :: Term_up -> Env -> Value
-- e is a checkable term, use its evaluator
eval_up (Ann e _) d = eval_dwn e d 
-- free variables are values
eval_up (Free x) d = vfree x
-- lookup via de Bruijn index
eval_up (Bound i) d = d !! i 
-- eval separatly then apply
eval_up (e :@: e') d = vapp (eval_up e d) (eval_dwn e' d)

--new
eval_up Star d = VStar
eval_up (Pi rho1 rho2) d = (VPi (eval_dwn rho1 d) (\x -> eval_dwn rho2 (x : d)))

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v -- use haskells evaluator
vapp (VNeutral n) v = VNeutral (NApp n v)

-- check
eval_dwn :: Term_dwn -> Env -> Value
-- Inf embeds inferable terms in Check terms, so call its evaluator
eval_dwn (Inf i) d = eval_up i d

-- evaluate body with extended context (using haskell function)
eval_dwn (Lam e) d = VLam(\x -> eval_dwn e (x : d))



type Type = Value
type Context = [(Name, Type)]


-------------------
-- Type Checking --
-------------------

type Result a = Either String a

-- type_up returns a type -- infer
-- type_down returns () -- check



type_up_zero :: Context -> Term_up -> Result Type
type_up_zero = type_up 0


type_up :: Int -> Context -> Term_up -> Result Type
-- annotated
-- evaluate the type in the empty context
type_up i gamma (Ann e rho) = do
                                type_dwn i gamma rho VStar
                                let t = eval_dwn rho []
                                type_dwn i gamma e t
                                return t
-- see if the type of the free variable is in the context                           
type_up i gamma (Free x) = case lookup x gamma of
                             Just t -> return t
                             Nothing -> throwError "Unknown Identifier"
type_up i gamma (e :@: e') = do 
                               -- infer the type of e
                               sigma <- type_up i gamma e
                               case sigma of 
                                   -- if e is a funtion type,
                                   --  check that the argument type is compatible
                                   --  if it is, return result type of application
                                   VPi t t' -> do type_dwn i gamma e' t 
                                                  return (t' (eval_dwn e' []))
                                   _ -> throwError "Illegal Application"
-- new
type_up i gamma Star = return VStar
type_up i gamma (Pi r r') = do type_dwn i gamma r VStar
                               let t = eval_dwn r []
                               type_dwn (i + 1) ((Local i,t) : gamma)
                                    (subst_dwn 0 (Free (Local i)) r') VStar
                               return VStar



type_dwn :: Int -> Context -> Term_dwn -> Type -> Result ()
-- check the infered type
type_dwn i gamma (Inf e) v = do 
                               v'<- type_up i gamma e
                               unless(quote_z v == quote_z v')(throwError "type mismatch")
-- check that lambda has function type
-- add binder to context with type
-- check the body with expanded context
type_dwn i gamma (Lam e) (VPi t t') = 
    type_dwn (i + 1) ((Local i, t) : gamma) 
        (subst_dwn 0 (Free (Local i)) e) (t' (vfree (Local i)))

type_dwn i gamma _ _ = throwError "type mismatch"                             
    
subst_up :: Int -> Term_up -> Term_up -> Term_up
subst_up i r (Ann e t) = Ann (subst_dwn i r e) t
subst_up i r (Bound j) = if i == j then r else Bound j
subst_up i r (Free y) = Free y
subst_up i r (e :@: e') = subst_up i r (e :@: subst_dwn i r e')
--new
subst_up i r Star = Star
subst_up i r (Pi t t') = Pi (subst_dwn i r t) (subst_dwn (i + 1) r t')

subst_dwn :: Int -> Term_up -> Term_dwn -> Term_dwn
subst_dwn i r (Inf e) = Inf (subst_up i r e)
subst_dwn i r (Lam e) = Lam (subst_dwn (i + 1) r e)


---------------
-- Quotation --
---------------

-- how to display a value (useful after evalutation and for fuction value)
quote_z :: Value -> Term_dwn
quote_z = quote 0

quote :: Int -> Value -> Term_dwn
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
-- new
quote i VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> Term_up
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> Term_up
boundfree i (Quote k) = Bound(i - k - 1)
boundfree i x = Free x

{-
recall
    const = \x -> \y -> x
    or
    const = VLam(\x -> (VLam(\y -> x)))

    quote_z (VLam(\x -> (VLam(\y -> x)))
=   Lam (quote 1 (VLam(\y -> vfree (Quote 0))))
=   Lam (Lam (quote 2 (vfree (Quote 0))))
=   Lam (Lam (neutralQuote 2 (NFree (Quote 0))))
=   Lam (Lam (Bound 1)) 

-}

{-
TODO
add Nat
add Vec
    as a practive for exploring elimination of dep types with a motive
add Eq

Questions:
    with dependent types, adding TApp and TAbs (polymorphims)
    isnt needed?
    what about kind KAbs and KApp?

    

-}