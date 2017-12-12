module Calculator_class where

------------------------------------------------------------------------
-- The Exp Type / abstract syntax trees to represent programs
------------------------------------------------------------------------

data Exp =
  C Int |                          -- constants
  V String |                       -- variables
  D String Exp |                   -- D x e declares variable x
                                   --   to have the value of expression e
  Let String Exp Exp |             -- let expressions
  Plus Exp Exp |                   -- addition
  Minus Exp Exp |                  -- subtraction
  Times Exp Exp |                  -- multiplication
  Div Exp Exp |                    -- integer division
  Eq Exp Exp |                     -- equality test
  If Exp Exp Exp |                 -- if-then-else
  Fun String String Exp |        -- function declaration
  Call String Exp |              -- function call
  Seq Exp Exp                      -- a sequencing operator
    deriving Show

-----------------------------------------------------------------------
-- The substitution function / used to evaluate function calls
-----------------------------------------------------------------------

-- here's a function to look up values in a list of name expression pairs.
--   if the name x is not found, just return the variable (V x)

safe_assoc [] x = V x
safe_assoc ((y,z):ys) x = if x == y then z else safe_assoc ys x

--------------------------------------------------------------------------
-- subst nes e  - nes is a list of pairs of names and expressions of the
--      form [(x1,e1), ... ,(xk,ek)].  For every variable (V xi) in e having
--      an entry (xi,ei) in the nes list, replace (V xi) in e by the
--      expression ei.  There is some complexity from avoiding variable
--      capture.
--------------------------------------------------------------------------


xs `minus` ys = filter (\x -> not (x `elem` ys))  xs

fv (C k)  = []
fv (V y) = [y]
fv (D x e1) = (x : (fv e1))
fv (Let y e1 e2) = (fv e1) ++ ((fv e2) `minus` [y])
fv (Plus e1 e2) = (fv e1) ++ (fv e2)
fv (Minus e1 e2) =  (fv e1) ++ (fv e2)
fv (Times e1 e2) =  (fv e1) ++ (fv e2)
fv (Div e1 e2) =  (fv e1) ++ (fv e2)
fv (Eq e1 e2) =  (fv e1) ++ (fv e2)
fv (If e1 e2 e3) = (fv e1) ++ (fv e2) ++ (fv e3)
fv (Fun name y e1) = fv e1 `minus` [y]
fv (Call name e1) = (fv e1)
fv (Seq  e1 e2) =  (fv e1) ++ (fv e2)


fresh x vars = if (x `elem` vars) then fresh (x ++ "'") vars else x

subst (z,e) (C k)  = C k
subst (z,e) (V y) = if y == z then e else (V y) 
subst (z,e) (D x e1) = D x (subst (z,e) e1)
-- Let depends on the capture avoidance used in the Fun case.
-- interpret Let y = e1 in e2   as ((\y _. e2) e1)
subst (z,e) (Let y e1 e2) = 
     let (Fun _ y' e2') = subst (z,e) (Fun "" y e2) in
         Let y' (subst (z,e) e1) e2'
subst (z,e) (Plus e1 e2) = Plus (subst (z,e) e1)(subst (z,e) e2)
subst (z,e) (Minus e1 e2) = Minus (subst (z,e) e1)(subst (z,e) e2)
subst (z,e) (Times e1 e2) = Times (subst (z,e) e1)(subst (z,e) e2)
subst (z,e) (Div e1 e2) = Div (subst (z,e) e1)(subst (z,e) e2)
subst (z,e) (Eq e1 e2) = Eq (subst (z,e) e1)(subst (z,e) e2)
subst (z,e) (If e1 e2 e3) = If (subst (z,e) e1)(subst (z,e) e2) (subst (z,e) e3)
subst (z,e) (Fun name y e1) = 
      if z == y then
         (Fun name y e1)
      else if y `elem` (fv e) then
         let w = fresh "w" (name:z:y:(fv e) ++ (fv e1)) in
           Fun name w (subst (z,e) (subst (y, V w) e1))
      else
         Fun name y (subst (z,e) e1)
subst (z,e) (Call name e1) = Call name  (subst (z,e) e1)
subst (z,e) (Seq  e1 e2) = Seq  (subst (z,e) e1)   (subst (z,e) e2)

------------------------------------------------------------------------
-- The Assignment Type / for remembering the values of variables and functions
-----------------------------------------------------------------------
-- Assignments contain 2 parts
-- val - an association list for looking up variable values
-- fun - an association list for looking up functions
--        for an Asignment a, the return value of (a fun f) is a triple
--        (i, args, body) where i is the number of arguments, args is a
--        list of arguments, and body is the body of the function f.

data Asssignment = A {val:: [(String, Int)], fun ::[(String,(String, Exp))]} deriving Show

assoc [] x = error ("assoc: " ++ x ++ " not found.")
assoc ((y,z):ys) x = if x == y then z else assoc ys x


-- a0 is an empty Assignment
a0 = A {val = [], fun = []}

-- the functions to add a value to the val part of an Assignment 
update_val a (x,v) = a {val = ((x,v) : (val a))}
get_val a x  = assoc (val a) x

-- the functions 
update_fun a (f,(parm,body))  = a {fun = ((f,(parm,body)) : (fun a))}
get_fun a x = assoc (fun a) x


-- We interpret intergers as Boolean values as in C++
--   false is 0 
--   true - is any non-zero value
true b = (b /= 0)
false b = (b == 0)

------------------------------------------------------------------------------
-- Expression Evaluator / eval is a function to evaluate expressions
------------------------------------------------------------------------------
-- eval a e - evalutes expression e using Assignment a
--            it retuens a pair (i,a) where i is the result of evaluating
--            expression e and a is the assignment generated by evaluating
--            e.  Note that for example (eval a (Fun "id" ["x"] (V x))
--            is the identity function and will update the assignment.
------------------------------------------------------------------------------
-- to evaluate a constant - just return the value
eval a (C k) = (k, a)

-- to evaluate a variable (V x) lookup the value of x in the assignment a
eval a (V x) = (get_val a x, a)

-- to evaluate a variable declaration (A x e), evaluate e resulting in
--      a pair (k, a1). Update the assignment a1 so that x is bound to k in
--      the new assignment.
eval a (D x e) = (k, a2)
     where (k, a1) = eval a e
           a2 = update_val a1 (x, k)

-- to evaluate (Let x e1 e2) evaluate e2 in the assignment a2 which has
--                  been updated to have x bound to the result of
--                  of evaluating e1 in assignment a.
eval a (Let x e1 e2) =  eval a2 e2
     where (k, a1)  = eval a e1
           a2 =  update_val a1 (x,k)

--  to evaluate (Plus e1 e2) evaluate e1 resulting in the value j
--          and possibly new assignment a1, then use a1 to evaluate e2
--          resulting in the value k and assignment a2. Return (j+k)
--          paired with the assignment a2.
eval a (Plus e1 e2) = (j + k, a2)
     where (j, a1) = eval a e1
           (k, a2) = eval a1 e2

--  to evaluate (Minus e1 e2) evaluate e1 resulting in the value j
--          and possibly new assignment a1, then use a1 to evaluate e2
--          resulting in the value k and assignment a2. Return (j-k)
--          paired with the assignment a2.
eval a (Minus e1 e2) = (j - k, a2)
     where (j, a1) = eval a e1 
           (k, a2) = eval a1 e2 

--  to evaluate (Times e1 e2) evaluate e1 resulting in the value j
--          and possibly new assignment a1, then use a1 to evaluate e2
--          resulting in the value k and assignment a2. Return (j * k)
--          paired with the assignment a2.

eval a (Times e1 e2) = (j * j, a2)
     where (j, a1) = eval a e1
           (k, a2) = eval a1 e2
                           
--  to evaluate (Div e1 e2) evaluate e1 resulting in the value j
--          and possibly new assignment a1, then use a1 to evaluate e2
--          resulting in the value k and assignment a2. Return (j `div` k)
--          paired with the assignment a2.
eval a (Div e1 e2) = (v1 `div` v2, a2)
     where (v1, a1) = eval a e1
           (v2, a2) = eval a1 e2                            

eval a (Eq e1 e2) = (v, a2)
     where v = if v1 == v2 then 1 else 0
           (v1, a1) = eval a e1 
           (v2, a2) = eval a1 e2

--  to evaluate (If e1 e2 e3) evaluate e1 resulting in the value b
--          (an integer interpreted as a Boolean).  There will be a
--          possibly new assignment a1. Then, of b is true,  use a1
--          to evaluate e2 using a1, if b is not true, then evaluate
--          e3 using assignment a1.

eval a (If e1 e2 e3) = if true b then (eval a1 e2) else (eval a1 e3)
     where (b, a1) = eval a e1

-- to evaluate a function declaration (Fun f parameterss e), update the fun
--         part of the assignment a so that f is bound to the pair
--         (parameters, e) where parameters is the
--         list of parameter names, and e is the body of the function f.
--         Arbitraily, return 1 (true) as the dummy value.

eval a (Fun f parameter body) = (1, update_fun a (f, (parameter, body)))

-- to evalue a function call (Call f args) - lookup f in the fun part of
--         assignment a. If f is in the assignment, the lookup will return
--         a triple (parameters, body) where parameters is the list of
--         parameter names, and body is the expression defining the body of f.
--         If the length of the list args is not the same as the langth of
--         list parameters, return an error.
eval a (Call f e) = eval a (subst (x,e) body)
     where (x, body) = get_fun a f

eval a (Seq e1 e2) = eval a1 e2
     where ( _ , a1) = eval a e1