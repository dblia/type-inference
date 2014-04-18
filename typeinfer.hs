{-# OPTIONS_GHC -O2 -optc-O2 #-}

module Main where

import Char (isAlpha, isAlphaNum)

type Id = Int
type Context = [(String, Id)] -- Gamma set
type Constraint = (Type, Type)

-- Lambda expressions
data Expr = EVar String | EAbs String Expr | EApp Expr Expr
    deriving Eq
-- Type expression
data Type = TVar Id | TArrow Type Type
    deriving Eq
-- Annotated expressions
data AExpr = AVar Id Type | AAbs Id AExpr Type | AApp AExpr AExpr Type

-- Parsing of expressions
instance Read Expr where
  readsPrec _ s =
    readParen True (\s -> [(EAbs x e, r)    |  ("\\", t1)  <-  lex s,
                                               (x, t2)     <-  lex t1, isVar x,
                                               (".", t3)   <-  lex t2,
                                               (e, r)      <-  readsPrec 0 t3] ++
                          [(EApp e1 e2, r)  |  (e1, t)     <-  readsPrec 0 s,
                                               (e2, r)     <-  readsPrec 0 t]) s ++
                          [(EVar x, r)      |  (x, r)      <-  lex s, isVar x]
    where isVar :: String -> Bool
          isVar x = isAlpha (head x) && all isAlphaNum x

-- Pretty printing of expressions
instance Show Expr where
  showsPrec p (EVar x) = (x ++)
  showsPrec p (EAbs x e) = showParen (True || p > 0) ((("\\" ++ x ++ ". ") ++) . showsPrec 0 e)
  showsPrec p (EApp e1 e2) = showParen (True || p > 1) (showsPrec 1 e1 . (" " ++) . showsPrec 2 e2)

-- Pretty printing of Types
instance Show Type where
  showsPrec p (TVar alpha) = ("@" ++) . showsPrec 0 alpha
  showsPrec p (TArrow sigma tau) = showParen (p > 0) (showsPrec 1 sigma . (" -> " ++) . showsPrec 0 tau)

-- Pretty printing of annotated expressions
instance Show AExpr where
  showsPrec p (AVar x t) = ("AVar" ++) . showParen (True) (showsPrec 0 x . (", " ++) . showsPrec 1 t)
  showsPrec p (AAbs x ae t) = ("Abs" ++) . showParen (True) (showsPrec 0 x . (", " ++) . 
      showParen (True) (showParen (p > 0) (showsPrec 1 ae)) . (", " ++) . showsPrec 0 t)
  showsPrec p (AApp ae1 ae2 t) = ("App" ++) . showParen (True) (showsPrec 0 ae1 . (", " ++) . 
      showsPrec 0 ae2 . (", " ++) . showsPrec 0 t)

-- Works as the 'elem' function but for Type type only.
typeElem :: Type -> Type -> Bool
typeElem t t'@(TVar _)
    | t == t' = True
    | otherwise = False
typeElem t t'@(TArrow t1 t2) = t == t' || typeElem t t1 || typeElem t t2

-- Given an AExpr return it's Type
getTypeOf :: AExpr -> Type
getTypeOf ae = 
    case ae of
         AVar _ t -> t
         AAbs _ _ t -> t
         AApp _ _ t -> t

-- Annotate epxressions with Types
annotate :: Id -> Expr -> Context -> (AExpr, Id, Context)
annotate i e gamma = 
    case e of
         EVar x -> 
            case (lookup x gamma) of
                Just t -> (AVar t (TVar t), i, gamma)
                Nothing -> error "type error"       -- free variable (Not in scope: `x')
         EAbs x e' -> (AAbs i ae' arrow, i', gamma')
            where (ae', i', gamma') = annotate (i+1) e' ((x, i) : gamma)
                  arrow = TArrow (TVar i) (getTypeOf ae')
         EApp ae1 ae2 -> (AApp ae1' ae2' (TVar i), i'', gamma)
            where (ae1', i', gamma') = annotate (i+1) ae1 gamma
                  (ae2', i'', gamma'') = annotate i' ae2 gamma

-- Generate the constraints from the annotated function 
-- see lecture typeInfer (p. 41)
constraints :: [AExpr] -> [Constraint] -> [Constraint]
constraints ae u =
    case ae of 
         [] -> u
         ((AVar _ _) : r) -> constraints r u
         ((AAbs _ ae' _) : r) -> constraints (ae' : r) u
         ((AApp ae1 ae2 t) : r) -> constraints (ae1 : ae2 : r) ((t1, TArrow t2 t) : u)
            where t1 = getTypeOf ae1
                  t2 = getTypeOf ae2

-- Apply a substitution to a given Type
substApply :: Constraint -> Type -> Type
substApply (a,t) t'@(TVar _)
    | a == t' = t
    | otherwise = t'
substApply t'@(a,t) (TArrow t1 t2) = TArrow nt1 nt2
    where nt1 = substApply t' t1
          nt2 = substApply t' t2

-- Algorithm W (lecture typeInfer (p. 42))
unify :: [Constraint] -> Type -> Maybe Type
unify [] u = Just u
unify ((t1,t2) : c) u
    | t1 == t2 = unify c u
unify ((t1@(TVar _), t2) : c) u          -- circularity check
    | not $ typeElem t1 t2 = unify c' u'
    where c' = map (\(x, y) -> (substApply (t1,t2) x, substApply (t1,t2) y)) c  -- apply substit to the constraint set
          u' = substApply (t1,t2) u      -- apply substit to the final type (u)
unify ((t1, t2@(TVar _)) : c) u          -- circularity check
    | not $ typeElem t2 t1 = unify c' u'
    where c' = map (\(x, y) -> (substApply (t2,t1) x, substApply (t2,t1) y)) c  -- apply substit to the constraint set
          u' = substApply (t2,t1) u      -- apply substit to the final type (u)
unify ((t1@(TArrow t11 t12), t2@(TArrow t21 t22)) : c) u = unify c' u
    where c' = (t11,t21) : (t12, t22) : c
unify _ _ = Nothing

-- Print the final Type in lexicographical order
lexicographic :: Type -> [(Id, Id)] -> Id -> (Type, [(Id, Id)], Id)
lexicographic (TVar x) hash i =
    case (lookup x hash) of
         Just t -> (TVar t, hash, i)
         Nothing -> (TVar i, (x, i) : hash, i+1)
lexicographic (TArrow t1 t2) hash i = (TArrow nt1 nt2, hash'', i'')
    where (nt1, hash', i') = lexicographic t1 hash i
          (nt2, hash'', i'') = lexicographic t2 hash' i'

-- Main program
main :: IO [()]
main = do
    n <- readLn  -- get the number of the lamda expressions
    count n readOne
    where count :: (Monad m) => Int -> m a -> m [a]
          count n m = sequence $ take n $ repeat m

readOne :: IO ()
readOne = do
    s <- getLine
    let e = read s :: Expr
        (ae, _, _) = annotate 0 e []  -- annotate the expr to type
        c = constraints [ae] []       -- get the constraints from the annotated function
        tyae = getTypeOf ae           -- the function type where we'll apply the substitution
        res = unify c tyae
    case res of
        Just t -> let (ty, _, _) = lexicographic t [] 0
                  in putStrLn $ show ty
        Nothing -> putStrLn "type error"
